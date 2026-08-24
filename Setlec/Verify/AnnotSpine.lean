import Setlec.Verify.BetaSpine
import Setlec.Verify.BinderLoop

/-!
# The application-annotation spine loop (task #96)

`annotateBodyI`'s app case walks a whole application spine once: the
head is annotated and inferred once and its Π-telescope is peeled
against the arguments with deferred substitution, replaying the
chained body's per-application checks (annotate the argument, infer
it, check it against the substituted domain, rebuild) in the chained
order.  The chained recursion instead inferred **every spine prefix**
(quadratic re-walks).

This file provides the pure mirror (`annotateSpine`/`annotateApp`,
generic over the core record, like `BetaSpine`'s) and the **soundness
of the loop against the chained spec**: a successful mirror run at the
pure fueled knot is reproduced by the original
one-application-at-a-time body at some fuel
(`annotateApp_sound_body`).  The interned walk
(`Setlec/Verify/DiscI6.lean`) composes its simulation against the
mirror with this theorem, so the `Expr`-level specification — and
everything above it — is unchanged.

Key steps of the reproduction (forward induction over the spine):

* the chained `infer` of an annotated prefix is value-determined by
  the loop state — `inferBody_app_pure` + one `inferStep` extend the
  prefix-type fact `infer cur = ty.instantiateList acc` by one
  argument (the loop's per-argument facts discharge `inferStep`'s
  possibly-Prop-gated re-check);
* the chained `whnf` between prefix inference and `∀`-view is the
  identity on a syntactic `∀` (`whnf_forallE`), so syntactic peeling
  skips it; a non-syntactic step ran the same `whnf` as the chained
  body (determinism + fuel monotonicity align them).
-/

namespace Setlec

open Expr

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The pure mirrors -/

/-- Pure mirror of the interned annotation spine loop
`annotateSpineI`: `ty` is the raw Π-telescope after the binders
consumed so far, `acc` their (annotated) arguments innermost first,
`cur` the annotated spine so far, `a'` the current argument, already
annotated, `rest` the raw remaining arguments. -/
def annotateSpine (r : CoreFns m) (depth : Nat) :
    Expr → List Expr → Expr → Expr → List Expr → m Expr
  | ty, acc, cur, a', rest =>
    match ty with
    | .forallE _ dom body _ => do
      let ta ← r.infer depth a'
      unless ← r.defeq depth ta (dom.instantiateList acc) do
        throw (.invalid "application argument type mismatch")
      match rest with
      | [] => pure (.app cur a')
      | b :: rest' => do
        let b' ← r.annotate depth b
        annotateSpine r depth body (a' :: acc) (.app cur a') b' rest'
    | ty => do
      match ← r.whnf depth (ty.instantiateList acc) with
      | .forallE _ dom body _ => do
        let ta ← r.infer depth a'
        unless ← r.defeq depth ta dom do
          throw (.invalid "application argument type mismatch")
        match rest with
        | [] => pure (.app cur a')
        | b :: rest' => do
          let b' ← r.annotate depth b
          annotateSpine r depth body [a'] (.app cur a') b' rest'
      | _ => throw (.invalid "function expected")

/-- Pure mirror of `annotateBodyI`'s app case: annotate the head, and
— preserving the chained order — annotate the first argument before
inferring the head's type, then walk the spine. -/
def annotateApp (r : CoreFns m) (depth : Nat) (h : Expr)
    (args : List Expr) : m Expr := do
  let h' ← r.annotate depth h
  match args with
  | [] => pure h'
  | a :: rest => do
    let a' ← r.annotate depth a
    let th ← r.infer depth h'
    annotateSpine r depth th [] h' a' rest

/-- The syntactic-`∀` arm of `annotateSpine`. -/
def annotateSpinePi (r : CoreFns m) (depth : Nat) (dom body : Expr)
    (acc : List Expr) (cur a' : Expr) (rest : List Expr) : m Expr := do
  let ta ← r.infer depth a'
  unless ← r.defeq depth ta (dom.instantiateList acc) do
    throw (.invalid "application argument type mismatch")
  match rest with
  | [] => pure (.app cur a')
  | b :: rest' => do
    let b' ← r.annotate depth b
    annotateSpine r depth body (a' :: acc) (.app cur a') b' rest'

/-- The normalize-and-retry arm of `annotateSpine`. -/
def annotateSpineWhnf (r : CoreFns m) (depth : Nat) (ty : Expr)
    (acc : List Expr) (cur a' : Expr) (rest : List Expr) : m Expr := do
  match ← r.whnf depth (ty.instantiateList acc) with
  | .forallE _ dom body _ => do
    let ta ← r.infer depth a'
    unless ← r.defeq depth ta dom do
      throw (.invalid "application argument type mismatch")
    match rest with
    | [] => pure (.app cur a')
    | b :: rest' => do
      let b' ← r.annotate depth b
      annotateSpine r depth body [a'] (.app cur a') b' rest'
  | _ => throw (.invalid "function expected")

theorem annotateSpine_pi (r : CoreFns m) (depth : Nat) (n : Name)
    (dom body : Expr) (bi : BinderMeta) (acc : List Expr)
    (cur a' : Expr) (rest : List Expr) :
    annotateSpine r depth (.forallE n dom body bi) acc cur a' rest
      = annotateSpinePi r depth dom body acc cur a' rest := by
  rw [annotateSpine.eq_def]
  rfl

theorem annotateSpine_ne_pi (r : CoreFns m) (depth : Nat) {ty : Expr}
    (acc : List Expr) (cur a' : Expr) (rest : List Expr)
    (hty : ∀ n dom body bi, ty ≠ Expr.forallE n dom body bi) :
    annotateSpine r depth ty acc cur a' rest
      = annotateSpineWhnf r depth ty acc cur a' rest := by
  cases ty with
  | forallE n dom body bi => exact absurd rfl (hty n dom body bi)
  | _ =>
    rw [annotateSpine.eq_def]
    rfl

/-! ## Fuel-indexed spellings -/

section AtF

variable {env : Env}

theorem annotateSpine_atF (d : Nat) :
    ∀ (rest : List Expr) (ty : Expr) (acc : List Expr)
      (cur a' : Expr) (F : Nat),
      (annotateSpine (fueledFns env) d ty acc cur a' rest).val F
        = annotateSpine (pureFns env F) d ty acc cur a' rest
  | rest, ty, acc, cur, a', F => by
    by_cases hpi : ∃ n dom body bi, ty = Expr.forallE n dom body bi
    · obtain ⟨n, dom, body, bi, rfl⟩ := hpi
      rw [annotateSpine_pi, annotateSpine_pi]
      unfold annotateSpinePi
      rw [FueledM.atF_bind]
      congr 1
      funext ta
      rw [FueledM.atF_bind]
      congr 1
      funext b
      cases b with
      | false => rfl
      | true =>
        cases rest with
        | nil => rfl
        | cons b rest' =>
          show ((fueledFns env).annotate d b >>= fun b' =>
            annotateSpine (fueledFns env) d body (a' :: acc)
              (.app cur a') b' rest').val F = _
          rw [FueledM.atF_bind]
          congr 1
          funext b'
          rw [annotateSpine_atF d rest' body (a' :: acc) (.app cur a') b' F]
    · have hty : ∀ n dom body bi, ty ≠ Expr.forallE n dom body bi :=
        fun n dom b bi hh => hpi ⟨n, dom, b, bi, hh⟩
      rw [annotateSpine_ne_pi _ _ _ _ _ _ hty,
        annotateSpine_ne_pi _ _ _ _ _ _ hty]
      unfold annotateSpineWhnf
      rw [FueledM.atF_bind]
      congr 1
      funext w
      cases w with
      | forallE n dom body bi =>
        dsimp only
        rw [FueledM.atF_bind]
        congr 1
        funext ta
        rw [FueledM.atF_bind]
        congr 1
        funext b
        cases b with
        | false => rfl
        | true =>
          cases rest with
          | nil => rfl
          | cons b rest' =>
            show ((fueledFns env).annotate d b >>= fun b' =>
              annotateSpine (fueledFns env) d body [a']
                (.app cur a') b' rest').val F = _
            rw [FueledM.atF_bind]
            congr 1
            funext b'
            rw [annotateSpine_atF d rest' body [a'] (.app cur a') b' F]
      | _ => rfl
  termination_by rest => rest.length

theorem annotateApp_atF (d : Nat) (h : Expr) (args : List Expr)
    (F : Nat) :
    (annotateApp (fueledFns env) d h args).val F
      = annotateApp (pureFns env F) d h args := by
  unfold annotateApp
  rw [FueledM.atF_bind]
  congr 1
  funext h'
  cases args with
  | nil => rfl
  | cons a rest =>
    show ((fueledFns env).annotate d a >>= fun a' =>
      (fueledFns env).infer d h' >>= fun th =>
      annotateSpine (fueledFns env) d th [] h' a' rest).val F = _
    rw [FueledM.atF_bind]
    congr 1
    funext a'
    rw [FueledM.atF_bind]
    congr 1
    funext th
    rw [annotateSpine_atF]

end AtF

/-! ## Soundness against the chained body -/

section Sound

variable {env : Env}

/-- `annotateBody`'s app case at the pure knot, exposed (stated at
`CheckM`, where the do-notation reduces). -/
theorem annotateCore_app_eq (F d : Nat) (f a : Expr) :
    annotateCore env (F + 1) d (.app f a)
      = (annotateCore env F d f >>= fun f' =>
         annotateCore env F d a >>= fun a' =>
         inferTypeCore env F d f' >>= fun tf =>
         whnf env F d tf >>= fun w =>
         match w with
         | .forallE _ ty _ _ =>
           inferTypeCore env F d a' >>= fun ta =>
           isDefEqCore env F d ta ty >>= fun ok =>
           if ok then pure (Expr.app f' a')
           else throw (.invalid "application argument type mismatch")
         | _ => throw (.invalid "function expected")) := by
  rw [annotateCore_succ]
  simp only [annotateBody, annotate_def, infer_def, whnf_def, defeq_def,
    Bind.bind, Except.bind]
  cases annotateCore env F d f with
  | error e => rfl
  | ok f' =>
    cases annotateCore env F d a with
    | error e => rfl
    | ok a' =>
      cases inferTypeCore env F d f' with
      | error e => rfl
      | ok tf =>
        cases whnf env F d tf with
        | error e => rfl
        | ok w =>
          cases w with
          | forallE n ty body mb =>
            dsimp only
            cases inferTypeCore env F d a' with
            | error e => rfl
            | ok ta =>
              cases isDefEqCore env F d ta ty with
              | error e => rfl
              | ok b => cases b <;> rfl
          | _ => rfl

/-- One chained application step: the chained body on `.app p a`
succeeds given the loop-state facts — prefix annotation, prefix-type
value `tf`, its `whnf` view as a `∀` with domain `dom`, and the
argument's annotation, inference and domain check. -/
private theorem annotateStep_chain {d : Nat} {p a cur a' : Expr}
    {tf dom : Expr}
    (h₀ : ∃ F, annotateCore env F d p = .ok cur)
    (h₁ : ∃ F, annotateCore env F d a = .ok a')
    (h₂ : ∃ F, inferTypeCore env F d cur = .ok tf)
    (hwhnf : ∃ F n body bi, whnf env F d tf
      = .ok (.forallE n dom body bi))
    (hchk : ∃ F ta, inferTypeCore env F d a' = .ok ta ∧
      isDefEqCore env F d ta dom = .ok true) :
    ∃ F, annotateCore env F d (.app p a) = .ok (.app cur a') := by
  obtain ⟨F₀, h₀⟩ := h₀
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨Fw, n, body, bi, hw⟩ := hwhnf
  obtain ⟨F₃, ta, hta, hb⟩ := hchk
  refine ⟨(max (max (max (max F₀ F₁) F₂) Fw) F₃) + 1, ?_⟩
  rw [annotateCore_app_eq]
  rw [annotateCore_mono (by omega) h₀, okB_bind,
    annotateCore_mono (by omega) h₁, okB_bind,
    inferTypeCore_mono (by omega) h₂, okB_bind,
    whnf_mono (by omega) hw, okB_bind]
  dsimp only
  rw [inferTypeCore_mono (by omega) hta, okB_bind,
    isDefEqCore_mono (by omega) hb, okB_bind]
  simp only [↓reduceIte]
  rfl

/-- The prefix-type fact extends by one argument: the chained `infer`
of the rebuilt application is one `inferStep` on the prefix type,
whose possibly-Prop-gated re-check is discharged by the loop's
per-argument facts. -/
private theorem inferStep_extend {d : Nat} {cur a' : Expr}
    {tf dom body : Expr} {n : Name} {bi : BinderMeta}
    (h₂ : ∃ F, inferTypeCore env F d cur = .ok tf)
    (hwhnf : ∃ F, whnf env F d tf = .ok (.forallE n dom body bi))
    (hchk : ∃ F ta, inferTypeCore env F d a' = .ok ta ∧
      isDefEqCore env F d ta dom = .ok true) :
    ∃ F, inferTypeCore env F d (.app cur a')
      = .ok (body.instantiate1 a') := by
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨Fw, hw⟩ := hwhnf
  obtain ⟨F₃, ta, hta, hb⟩ := hchk
  refine ⟨(max (max F₂ Fw) F₃) + 1, ?_⟩
  rw [inferTypeCore_succ, inferBody_app_pure, infer_def,
    inferTypeCore_mono (by omega) h₂, okB_bind]
  unfold inferStep
  rw [whnf_def, whnf_mono (by omega) hw, okB_bind]
  dsimp only
  by_cases hnz : codNonZero bi = true
  · rw [if_pos hnz]
    rfl
  · rw [if_neg hnz]
    rw [infer_def, inferTypeCore_mono (by omega) hta, okB_bind,
      defeq_def, isDefEqCore_mono (by omega) hb, okB_bind]
    simp only [↓reduceIte]
    rfl

/-- Forward induction over the spine: a successful loop run from a
chained-reproducible state is reproduced by the chained annotation of
the whole remaining application, at some fuel. -/
private theorem annotateSpine_sound_go {d : Nat} :
    ∀ (rest : List Expr) (ty : Expr) (acc : List Expr)
      (cur a' p a : Expr) (F : Nat) (vres : Expr),
      (∃ F₀, annotateCore env F₀ d p = .ok cur) →
      (∃ F₁, annotateCore env F₁ d a = .ok a') →
      (∃ F₂, inferTypeCore env F₂ d cur
        = .ok (ty.instantiateList acc)) →
      annotateSpine (pureFns env F) d ty acc cur a' rest = .ok vres →
      ∃ F', annotateCore env F' d (Expr.mkAppN (.app p a) rest)
        = .ok vres
  | rest, ty, acc, cur, a', p, a, F, vres => by
    intro h₀ h₁ h₂ H
    by_cases hpi : ∃ n dom body bi, ty = Expr.forallE n dom body bi
    · -- syntactic ∀: the chained whnf between prefix inference and
      -- view is the identity
      obtain ⟨n, dom, body, bi, rfl⟩ := hpi
      rw [annotateSpine_pi] at H
      unfold annotateSpinePi at H
      obtain ⟨ta, hta, H⟩ := bind_okB H
      rw [infer_def] at hta
      obtain ⟨b, hb, H⟩ := bind_okB H
      rw [defeq_def] at hb
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at H
        exact nomatch H
      | true =>
        simp only [↓reduceIte] at H
        have hwl : (Expr.forallE n dom body bi).instantiateList acc
            = .forallE n (dom.instantiateList acc)
              (body.instantiateList acc 1) bi := instList_forallE ..
        have hwhnf : ∃ F' n' body' bi',
            whnf env F' d ((Expr.forallE n dom body bi).instantiateList
              acc) = .ok (.forallE n' (dom.instantiateList acc)
                body' bi') :=
          ⟨2, n, body.instantiateList acc 1, bi, by
            rw [hwl]
            exact whnf_forallE 0 d n (dom.instantiateList acc)
              (body.instantiateList acc 1) bi⟩
        have hstep := annotateStep_chain h₀ h₁ h₂
          (by obtain ⟨F', n', body', bi', hh⟩ := hwhnf
              exact ⟨F', n', body', bi', hh⟩)
          ⟨F, ta, hta, hb⟩
        cases rest with
        | nil =>
          injection H with hres
          subst hres
          exact hstep
        | cons b rest' =>
          obtain ⟨b', hb', H⟩ := bind_okB H
          rw [annotate_def] at hb'
          have hty₂ : ∃ F₂', inferTypeCore env F₂' d (.app cur a')
              = .ok (body.instantiateList (a' :: acc)) := by
            obtain ⟨F₂', hh⟩ := inferStep_extend h₂
              ⟨2, by
                rw [hwl]
                exact whnf_forallE 0 d n (dom.instantiateList acc)
                  (body.instantiateList acc 1) bi⟩
              ⟨F, ta, hta, hb⟩
            exact ⟨F₂', by rw [instList_cons0]; exact hh⟩
          exact annotateSpine_sound_go rest' body (a' :: acc)
            (.app cur a') b' (.app p a) b F vres hstep ⟨F, hb'⟩ hty₂ H
    · -- non-syntactic step: substitute and normalize, as the chained
      -- body does
      have hty : ∀ n dom body bi, ty ≠ Expr.forallE n dom body bi :=
        fun n dom b bi hh => hpi ⟨n, dom, b, bi, hh⟩
      rw [annotateSpine_ne_pi _ _ _ _ _ _ hty] at H
      unfold annotateSpineWhnf at H
      obtain ⟨w, hw, H⟩ := bind_okB H
      rw [whnf_def] at hw
      cases w with
      | forallE n dom body bi =>
        dsimp only at H
        obtain ⟨ta, hta, H⟩ := bind_okB H
        rw [infer_def] at hta
        obtain ⟨b, hb, H⟩ := bind_okB H
        rw [defeq_def] at hb
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at H
          exact nomatch H
        | true =>
          simp only [↓reduceIte] at H
          have hstep := annotateStep_chain h₀ h₁ h₂
            ⟨F, n, body, bi, hw⟩ ⟨F, ta, hta, hb⟩
          cases rest with
          | nil =>
            injection H with hres
            subst hres
            exact hstep
          | cons b rest' =>
            obtain ⟨b', hb', H⟩ := bind_okB H
            rw [annotate_def] at hb'
            have hty₂ : ∃ F₂', inferTypeCore env F₂' d (.app cur a')
                = .ok (body.instantiateList [a']) := by
              obtain ⟨F₂', hh⟩ := inferStep_extend h₂ ⟨F, hw⟩
                ⟨F, ta, hta, hb⟩
              exact ⟨F₂', by rw [instList_single]; exact hh⟩
            exact annotateSpine_sound_go rest' body [a']
              (.app cur a') b' (.app p a) b F vres hstep ⟨F, hb'⟩
              hty₂ H
      | bvar i => exact nomatch H
      | fvar idx nm t => exact nomatch H
      | sort u => exact nomatch H
      | const nm us => exact nomatch H
      | app f' g' => exact nomatch H
      | lam nm t bb mb => exact nomatch H
      | letE nm t v bb => exact nomatch H
      | lit l => exact nomatch H
      | proj s i e => exact nomatch H
  termination_by rest => rest.length

/-- The bridge the interned walk uses: a successful spine-loop run on
the head's annotation and inferred type is reproduced by the chained
`annotateBody` on the whole application, at some fuel. -/
theorem annotateApp_sound_body (d : Nat) (fx ax : Expr) (vres : Expr)
    (F : Nat)
    (H : (annotateApp (fueledFns env) d (Expr.app fx ax).getAppFn
        (Expr.app fx ax).getAppArgs).val F = .ok vres) :
    ∃ F', (annotateBody (fueledFns env) env d (.app fx ax)).val F'
      = .ok vres := by
  rw [annotateApp_atF] at H
  unfold annotateApp at H
  obtain ⟨h', hh', H⟩ := bind_okB H
  rw [annotate_def] at hh'
  cases hargs : (Expr.app fx ax).getAppArgs with
  | nil =>
    exact absurd hargs (by simp [Expr.getAppArgs])
  | cons a rest =>
    rw [hargs] at H
    dsimp only at H
    obtain ⟨a', ha', H⟩ := bind_okB H
    rw [annotate_def] at ha'
    obtain ⟨th, hth, H⟩ := bind_okB H
    rw [infer_def] at hth
    obtain ⟨F', hchain⟩ := annotateSpine_sound_go rest th [] h' a'
      (Expr.app fx ax).getAppFn a F vres ⟨F, hh'⟩ ⟨F, ha'⟩
      ⟨F, by rw [Expr.instantiateList_nil]; exact hth⟩ H
    have hmk : Expr.mkAppN (.app (Expr.app fx ax).getAppFn a) rest
        = .app fx ax := by
      have hg := Expr.mkAppN_getApp (.app fx ax)
      rw [hargs] at hg
      exact hg
    rw [hmk] at hchain
    cases F' with
    | zero =>
      rw [annotateCore_zero] at hchain
      exact nomatch hchain
    | succ G =>
      refine ⟨G, ?_⟩
      rw [annotateBody_atF, ← annotateCore_succ]
      exact hchain

end Sound

end Setlec
