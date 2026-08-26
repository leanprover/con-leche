import Setlec.TTVerify.NatOpsStep

/-!
# The `infer` step of `CheckStepTT`

`InferClaimsTT` at `fuel + 1`: successful inference establishes a
typing.  Transpose of `infer_claims` (`Setlec/Model/Core/Infer.lean`).

**This is the quarter the governing directive is about.**  `inferBody`
has eleven clauses and each one is a single TT rule, so the bridge here
really does nothing clever: invert the checker's clause, apply the
induction hypotheses to the subterms, apply the rule.  The map is worth
writing down because it is the claim the design rests on:

| `inferBody` clause | rule |
|---|---|
| `.sort u` | `HasType.sort` |
| `.fvar idx _ ty` (in scope) | `HasType.bvar`, via `CtxOk` |
| `.const n us` | `EnvTT.has_type`, weakened |
| `.lit (.natVal _)` | `hasType_numeral` |
| `.lit (.strVal _)` | the string-literal typing |
| `.forallE` | `HasType.pi` |
| `.lam` | `HasType.lam` |
| `.app` | `HasType.app`, premise from the certificate |
| `.proj` | `projFst` / `projSnd` |
| `.letE` | `HasType.letE` |
| `.bvar` | throws |

`infer` takes **no precondition** (§12): it is the establisher, and
every premise its rules need comes from an induction hypothesis or from
the checker's own guard.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The leaf clauses -/

/-- `Sort u` infers `Sort (u+1)`, which is `HasType.sort`. -/
theorem infer_sort_claim {env : Env} {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {u : Level} {t : Expr}
    (h : inferTypeCore env (fuel + 1) d (.sort u) = .ok t) :
    ∃ v tv, denote cval env φ d (.sort u) = some v ∧
      denote cval env φ d t = some tv ∧ HasType Δ v tv := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind, Except.ok.injEq] at h
  subst h
  refine ⟨.sort (u.eval φ), .sort (u.eval φ + 1), ?_, ?_, .sort⟩
  · rw [denote_sort]
  · rw [denote_sort]
    rfl

/-- An in-scope free variable infers its annotation, which is
`HasType.bvar` — and the index arithmetic is exactly `CtxOk`'s. -/
theorem infer_fvar_claim {env : Env} {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {idx : Nat} {n : Name} {ty t : Expr}
    (h : inferTypeCore env (fuel + 1) d (.fvar idx n ty) = .ok t)
    (hC : CtxOk cval env φ d Δ (.fvar idx n ty)) :
    ∃ v tv, denote cval env φ d (.fvar idx n ty) = some v ∧
      denote cval env φ d t = some tv ∧ HasType Δ v tv := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · next hlt =>
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨hlt', -, A, hΔ, hty⟩ :=
      hC.2 (idx, n, ty) (by simp [Expr.fvarLeaves])
    refine ⟨.bvar (d - 1 - idx), A.liftN (d - idx), ?_, ?_, ?_⟩
    · rw [denote_fvar]
    · exact hty
    · have := HasType.bvar (Γ := Δ) (i := d - 1 - idx) (A := A) hΔ
      rwa [show d - 1 - idx + 1 = d - idx from by omega] at this
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A `Nat` literal infers `Nat`. -/
theorem infer_natLit_claim {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {d : Nat} {Δ : List VExpr} {k : Nat} {t : Expr}
    (h : inferTypeCore env (fuel + 1) d (.lit (.natVal k)) = .ok t) :
    ∃ v tv, denote m.cval env φ d (.lit (.natVal k)) = some v ∧
      denote m.cval env φ d t = some tv ∧ HasType Δ v tv := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · next hg =>
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨numeral k, natT, denote_natLit_numeral m φ hg d k, ?_, ?_⟩
    · rw [denote_natT_const m φ hg d]
    · exact hasType_numeral k
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `bvar` is outside the fragment; the checker throws, and the bridge
refutes it from the denotation as well. -/
theorem infer_bvar_claim {env : Env} {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {i : Nat} {t : Expr}
    (h : inferTypeCore env (fuel + 1) d (.bvar i) = .ok t) :
    ∃ v tv, denote cval env φ d (.bvar i) = some v ∧
      denote cval env φ d t = some tv ∧ HasType Δ v tv := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The frame conditions of an inferred type

Every structural clause recurses into a subterm and then into the type
it inferred for it, so both need their frame conditions.  Bundled once,
as for `reduceNat`. -/

/-- The frame conditions of an inferred type. -/
theorem frame_infer {env : Env} {cval : TConstVal} {φ : Name → Nat}
    (hwf : EnvWF env) {fuel d : Nat} {Δ : List VExpr} {e t : Expr}
    (h : inferTypeCore env fuel d e = .ok t)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOk cval env φ d Δ e) :
    Expr.WScoped d t ∧ t.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded t ∧ CtxOk cval env φ d Δ t :=
  ⟨inferTypeCore_WScoped hwf fuel h hws,
    inferTypeCore_looseBVars hwf fuel h hws hb hLb,
    fun l hl => hLb l (inferTypeCore_fvarLeaves hwf fuel h hws l hl),
    CtxOk.of_subset (inferTypeCore_fvarLeaves hwf fuel h hws) hC⟩

/-! ## The application clause

**The centre of the directive's claim.**  `inferBody`'s `.app` clause
is `HasType.app` and one certificate, and the proof below is exactly
that: two induction hypotheses, two `conv`s, one rule.  Nothing is
threaded, nothing is inverted, and the argument's typing is
re-established at the domain the redex names rather than carried from
above (§6). -/

/-- `.app` infers by `HasType.app`, its premise from the certificate. -/
theorem infer_app_claim {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT m φ fuel) (ihd : DefEqClaimsTT m φ fuel)
    (ihi : InferClaimsTT m φ fuel)
    {d : Nat} {Δ : List VExpr} {f a t : Expr}
    (h : inferTypeCore env (fuel + 1) d (.app f a) = .ok t)
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOk m.cval env φ d Δ (.app f a)) :
    ∃ v tv, denote m.cval env φ d (.app f a) = some v ∧
      denote m.cval env φ d t = some tv ∧ HasType Δ v tv := by
  obtain ⟨tf, n', ty', body', m', htf, hwf, rfl, ta, hta, hde⟩ :=
    inferTypeCore_app_inv h
  -- the two subterms' frame conditions
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCf : CtxOk m.cval env φ d Δ f :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCa : CtxOk m.cval env φ d Δ a :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  -- the head is typed at its inferred type…
  obtain ⟨vf, vtf, hvf, hvtf, hft⟩ := ihi htf hws.1 hb.1 hLf hCf
  obtain ⟨htfw, htfb, htfL, htfC⟩ := frame_infer m.wf htf hws.1 hb.1 hLf hCf
  -- …which reduces to a `∀`, so the head is typed at a `pi`
  obtain ⟨vpi, hvpi, hDpi⟩ := ihw hwf htfw htfb htfL htfC hvtf
  rw [denote_forallE] at hvpi
  split at hvpi
  · exact nomatch hvpi
  · next A hA =>
    split at hvpi
    · exact nomatch hvpi
    · next B hB =>
      obtain rfl : vpi = .pi A B := (Option.some.inj hvpi).symm
      have hfpi : HasType Δ vf (.pi A B) := Deq.conv hft hDpi
      -- the argument is typed at the domain the application names
      obtain ⟨va, vta, hva, hvta, hat⟩ := ihi hta hws.2 hb.2 hLa hCa
      obtain ⟨htaw, htab, htaL, htaC⟩ :=
        frame_infer m.wf hta hws.2 hb.2 hLa hCa
      have hwfe : Expr.WScoped d (Expr.forallE n' ty' body' m') :=
        whnf_WScoped m.wf fuel hwf htfw
      have hbfe : (Expr.forallE n' ty' body' m').looseBVarsBounded 0 = true :=
        whnf_looseBVars m.wf fuel hwf htfb
      have hLfe : Expr.LeavesBounded (.forallE n' ty' body' m') :=
        fun l hl => htfL l (whnf_fvarLeaves m.wf fuel hwf l hl)
      have hCfe : CtxOk m.cval env φ d Δ (.forallE n' ty' body' m') :=
        CtxOk.of_subset (whnf_fvarLeaves m.wf fuel hwf) htfC
      simp only [Expr.WScoped] at hwfe
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
      have hLty : Expr.LeavesBounded ty' := fun l hl =>
        hLfe l (by simp [Expr.fvarLeaves, hl])
      have hCty : CtxOk m.cval env φ d Δ ty' :=
        CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCfe
      have hDdom : Deq Δ vta A :=
        ihd hde htaw htab htaL hwfe.1 hbfe.1 hLty htaC hCty hvta hA
      have haA : HasType Δ va A := Deq.conv hat hDdom
      refine ⟨.app vf va, VExpr.inst B va, ?_, ?_, HasType.app hfpi haA⟩
      · rw [denote_app, hvf, hva]
      · rw [denote_beta (n := n') (ty := ty') hcl hwfe.2.fvarsBelow hws.2
          hb.2 hva 0, hB]
        rfl

/-! ## `ensureSort`, denoted

Three clauses reduce an inferred type to a sort.  The step is always
the same — the whnf claim, then `conv` — so it is one lemma. -/

/-- A subject whose inferred type reduces to a sort is typed at that
sort. -/
theorem hasType_of_ensureSort {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel d : Nat} {Δ : List VExpr} {te : Expr} {u : Level} {v tv : VExpr}
    (ihw : WhnfClaimsTT m φ fuel)
    (hens : ensureSortCore env fuel d te = .ok u)
    (hws : Expr.WScoped d te) (hb : te.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded te) (hC : CtxOk m.cval env φ d Δ te)
    (hte : denote m.cval env φ d te = some tv)
    (hv : HasType Δ v tv) : HasType Δ v (.sort (u.eval φ)) := by
  obtain ⟨w, hw, hD⟩ := ihw (ensureSortCore_inv hens) hws hb hLb hC hte
  rw [denote_sort] at hw
  obtain rfl : w = .sort (u.eval φ) := (Option.some.inj hw).symm
  exact Deq.conv hv hD

/-! ## The `let` clause

`HasType.letE` takes three premises and the checker supplies all three
in order: the annotation's sort from `ensureSort`, the value's typing
from the certificate, and the body's typing from the recursive
inference **on the substituted body** — which is what the rule types,
so no opening is needed on either side. -/

/-- `.letE` infers by `HasType.letE`. -/
theorem infer_letE_claim {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT m φ fuel) (ihd : DefEqClaimsTT m φ fuel)
    (ihi : InferClaimsTT m φ fuel)
    {d : Nat} {Δ : List VExpr} {n : Name} {ty val b t : Expr}
    (h : inferTypeCore env (fuel + 1) d (.letE n ty val b) = .ok t)
    (hws : Expr.WScoped d (.letE n ty val b))
    (hb : (Expr.letE n ty val b).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE n ty val b))
    (hC : CtxOk m.cval env φ d Δ (.letE n ty val b)) :
    ∃ v tv, denote m.cval env φ d (.letE n ty val b) = some v ∧
      denote m.cval env φ d t = some tv ∧ HasType Δ v tv := by
  obtain ⟨tty, s, tv, hty, hens, hvv, hde, hbody⟩ :=
    inferTypeCore_letE_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLval : Expr.LeavesBounded val := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCty : CtxOk m.cval env φ d Δ ty :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCval : CtxOk m.cval env φ d Δ val :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  -- premise one: the annotation is a type
  obtain ⟨A, vtty, hA, hvtty, hAt⟩ := ihi hty hws.1 hb.1.1 hLty hCty
  obtain ⟨httyw, httyb, httyL, httyC⟩ :=
    frame_infer m.wf hty hws.1 hb.1.1 hLty hCty
  have hAs : HasType Δ A (.sort (s.eval φ)) :=
    hasType_of_ensureSort m φ ihw hens httyw httyb httyL httyC hvtty hAt
  -- premise two: the value is at the annotation
  obtain ⟨xv, vtv, hxv, hvtv, hxvt⟩ := ihi hvv hws.2.1 hb.1.2 hLval hCval
  obtain ⟨htvw, htvb, htvL, htvC⟩ :=
    frame_infer m.wf hvv hws.2.1 hb.1.2 hLval hCval
  have hxvA : HasType Δ xv A :=
    Deq.conv hxvt (ihd hde htvw htvb htvL hws.1 hb.1.1 hLty htvC hCty
      hvtv hA)
  -- premise three: the substituted body, which is what the rule types
  have hwred : Expr.WScoped d (b.instantiate1 val) :=
    Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
  have hbred : (b.instantiate1 val).looseBVarsBounded 0 = true :=
    Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
  have hLred : Expr.LeavesBounded (b.instantiate1 val) := fun l hl => by
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · exact hLb l (by simp [Expr.fvarLeaves, h2])
    · exact hLval l h2
  have hCred : CtxOk m.cval env φ d Δ (b.instantiate1 val) := by
    refine ⟨hC.1, fun l hl => ?_⟩
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
    · exact hCval.2 l h2
  obtain ⟨bv, btv, hbv, hbtv, hbvt⟩ := ihi hbody hwred hbred hLred hCred
  -- the `let`'s own denotation, and the body's as its `inst`
  have hopen : ∃ B, denote m.cval env φ (d + 1)
      (b.instantiate1 (.fvar d n ty)) = some B ∧ VExpr.inst B xv = bv := by
    cases hB : denote m.cval env φ (d + 1)
        (b.instantiate1 (.fvar d n ty)) with
    | none =>
      rw [denote_beta (n := n) (ty := ty) hcl hws.2.2.fvarsBelow hws.2.1
        hb.1.2 hxv 0, hB] at hbv
      exact nomatch hbv
    | some B =>
      refine ⟨B, rfl, ?_⟩
      rw [denote_beta (n := n) (ty := ty) hcl hws.2.2.fvarsBelow hws.2.1
        hb.1.2 hxv 0, hB] at hbv
      exact (Option.some.inj hbv)
  obtain ⟨B, hB, rfl⟩ := hopen
  refine ⟨.letE A xv B, btv, ?_, hbtv, HasType.letE hAs hxvA hbvt⟩
  rw [denote_letE, hA, hxv, hB]

/-! ## The `∀` clause

The one clause that opens a binder, so the one that consumes
`CtxOk.open`.  `Level.imax`'s evaluation and the layer's `imax` are the
same function, so the result type matches on the nose. -/

/-- `.forallE` infers by `HasType.pi`. -/
theorem infer_forallE_claim {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel)
    {d : Nat} {Δ : List VExpr} {n : Name} {ty body t : Expr}
    {mb : BinderMeta}
    (h : inferTypeCore env (fuel + 1) d (.forallE n ty body mb) = .ok t)
    (hws : Expr.WScoped d (.forallE n ty body mb))
    (hb : (Expr.forallE n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.forallE n ty body mb))
    (hC : CtxOk m.cval env φ d Δ (.forallE n ty body mb)) :
    ∃ v tv, denote m.cval env φ d (.forallE n ty body mb) = some v ∧
      denote m.cval env φ d t = some tv ∧ HasType Δ v tv := by
  obtain ⟨tty, u, bt, v, hty, hwu, hbt, hens, rfl⟩ :=
    inferTypeCore_forall_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCty : CtxOk m.cval env φ d Δ ty :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCbody : CtxOk m.cval env φ d Δ body :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  -- the domain is a type
  obtain ⟨A, vtty, hA, hvtty, hAt⟩ := ihi hty hws.1 hb.1 hLty hCty
  obtain ⟨httyw, httyb, httyL, httyC⟩ :=
    frame_infer m.wf hty hws.1 hb.1 hLty hCty
  have hAs : HasType Δ A (.sort (u.eval φ)) := by
    obtain ⟨w, hw, hD⟩ := ihw hwu httyw httyb httyL httyC hvtty
    rw [denote_sort] at hw
    obtain rfl : w = .sort (u.eval φ) := (Option.some.inj hw).symm
    exact Deq.conv hAt hD
  -- open the binder and infer the codomain's sort
  have hwopen : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
    Expr.WScoped.instantiate1 hws.1 0 hws.2
  have hbopen : (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0
      = true :=
    looseBVarsBounded_instantiate1 body 0 hb.2
  have hLopen : Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) :=
    fun l hl => by
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
      · rw [Expr.fvarLeaves] at h2
        rcases List.mem_cons.mp h2 with rfl | h3
        · exact hb.1
        · exact hLty l h3
  have hCopen := CtxOk.open (n := n) hcl hCbody hCty hA hws.1.fvarsBelow
  obtain ⟨B, vbt, hB, hvbt, hBt⟩ := ihi hbt hwopen hbopen hLopen hCopen
  obtain ⟨hbtw, hbtb, hbtL, hbtC⟩ :=
    frame_infer m.wf hbt hwopen hbopen hLopen hCopen
  have hBs : HasType (A :: Δ) B (.sort (v.eval φ)) :=
    hasType_of_ensureSort m φ ihw hens hbtw hbtb hbtL hbtC hvbt hBt
  refine ⟨.pi A B, .sort (Setlec.TT.imax (u.eval φ) (v.eval φ)), ?_, ?_,
    HasType.pi hAs hBs⟩
  · rw [denote_forallE, hA, hB]
  · rw [denote_sort]
    rfl

/-! ## The constant clause

The one clause whose rule is not in `Setlec/TT/Judgment.lean` but in
the **environment invariant**: `EnvTT.has_type` is precisely "every
stored constant's valuation is derivably of its stored type", so the
clause is that field plus the two moves that get it from the empty
context at depth 0 to `Δ` at depth `d`.

Both moves are already built and neither is about constants:
`denote_instLevels` (level instantiation composes the assignment,
§8.7) and `denote_lift` at a closed denotation (`denote_closed`).
That the delta step and the constant clause need the same two lemmas
is not a coincidence — they are the same fact about `cval` read in two
directions. -/

/-- `.const` infers by `EnvTT.has_type`. -/
theorem infer_const_claim {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    {d : Nat} {Δ : List VExpr} {n : Name} {us : List Level} {t : Expr}
    (h : inferTypeCore env (fuel + 1) d (.const n us) = .ok t) :
    ∃ v tv, denote m.cval env φ d (.const n us) = some v ∧
      denote m.cval env φ d t = some tv ∧ HasType Δ v tv := by
  rw [inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  cases hf : env.find? n with
  | none => rw [hf] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    rw [hf] at h
    dsimp only at h
    split at h
    · next hlen =>
      simp only [Except.ok.injEq] at h
      subst h
      -- the stored name is this one, and the environment types it
      obtain rfl : ci.name = n := by
        rw [Env.find?] at hf
        have := List.find?_some hf
        simpa using this
      obtain ⟨tv0, htv0, hct⟩ :=
        m.has_type ci (find?_mem hf)
          (Level.substFn φ ci.toConstantVal.levelParams us)
      -- the stored type is closed, so its denotation is
      obtain ⟨hnf, -, -, hbd, -⟩ := m.wf ci (find?_mem hf)
      have hcls : VExpr.Closed tv0 := denote_closed hcl hnf hbd htv0
      refine ⟨m.cval ci.name
        (Level.substFn φ ci.toConstantVal.levelParams us), tv0, ?_, ?_, ?_⟩
      · rw [denote_const, hf]
        exact if_pos hlen
      · rw [denote_instLevels m.val_params,
          denote_lift hcl
            (Expr.WScoped.of_not_hasFvar hnf).fvarsBelow d (Nat.zero_le d)]
        rw [denoteClosed] at htv0
        rw [htv0]
        simp only [Option.map_some, Nat.sub_zero,
          VExpr.liftN_eq_self_of_closed hcls]
      · exact HasType.weakenNil hct Δ
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The `λ` clause

The checker infers the body's type in the opened context and then
**abstracts** it back under the binder, so the bridge has to undo that
round trip: `denote` of `(bt.abstract1 d).instantiate1 (.fvar d n ty)`
must be `denote` of `bt`.  It is — `abstract1_instantiate1`
(`Setlec/Verify/Abstract.lean`) — provided every `fvar` at index `d` in
`bt` carries this binder's name and annotation, which is
`Expr.fvarConsistent`.

That side condition costs nothing here, and the reason is the leaf
discipline: the inferred type's leaves are a subset of the subject's
(`inferTypeCore_fvarLeaves`), the subject is the *opened* body, and its
only leaf at index `d` is the variable the opening inserted.  So the
condition is discharged from the same lemma the frame conditions use.

Note what is **not** needed: `HasType.lam` carries no domain premise,
so the checker's `whnf (infer ty) = .sort _` guard is not consumed at
all — it is a well-formedness check the layer does not ask for.  This
is the `Typable.lamBody` gap of `Setlec/TTVerify/Typable.lean` seen
from the producing side. -/

/-- `.lam` infers by `HasType.lam`. -/
theorem infer_lam_claim {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihi : InferClaimsTT m φ fuel)
    {d : Nat} {Δ : List VExpr} {n : Name} {ty body t : Expr}
    {mb : BinderMeta}
    (h : inferTypeCore env (fuel + 1) d (.lam n ty body mb) = .ok t)
    (hws : Expr.WScoped d (.lam n ty body mb))
    (hb : (Expr.lam n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.lam n ty body mb))
    (hC : CtxOk m.cval env φ d Δ (.lam n ty body mb)) :
    ∃ v tv, denote m.cval env φ d (.lam n ty body mb) = some v ∧
      denote m.cval env φ d t = some tv ∧ HasType Δ v tv := by
  obtain ⟨tty, u, bt, hty, hwu, hbt, rfl⟩ := inferTypeCore_lam_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCty : CtxOk m.cval env φ d Δ ty :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCbody : CtxOk m.cval env φ d Δ body :=
    CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  obtain ⟨A, vtty, hA, -, -⟩ := ihi hty hws.1 hb.1 hLty hCty
  -- open the binder and infer the body's type there
  have hwopen : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
    Expr.WScoped.instantiate1 hws.1 0 hws.2
  have hbopen : (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0
      = true := looseBVarsBounded_instantiate1 body 0 hb.2
  have hLopen : Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) :=
    fun l hl => by
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · exact hLb l (by simp [Expr.fvarLeaves, h2])
      · rw [Expr.fvarLeaves] at h2
        rcases List.mem_cons.mp h2 with rfl | h3
        · exact hb.1
        · exact hLty l h3
  have hCopen := CtxOk.open (n := n) hcl hCbody hCty hA hws.1.fvarsBelow
  obtain ⟨B, vbt, hB, hvbt, hBt⟩ := ihi hbt hwopen hbopen hLopen hCopen
  -- the abstraction round trip is the identity on the inferred type
  have hleaf : Expr.LeafCond d n ty (body.instantiate1 (.fvar d n ty)) := by
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
  refine ⟨.lam A B, .pi A vbt, ?_, ?_, HasType.lam hBt⟩
  · rw [denote_lam, hA, hB]
  · rw [denote_forallE, hA, hround, hvbt]

end Setlec.TTVerify
