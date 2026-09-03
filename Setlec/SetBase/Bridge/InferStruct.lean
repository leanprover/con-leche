import Setlec.SetBase.Bridge.ReduceNat

/-!
# The structural inference clauses (task #148, T3, batches a-rest + b)

I6 `pi`, I7 `lam`, I8 `app`, I10 `letE` — the four clauses that were
held by the slack/`Red` finding, written straight through against the
settled shapes (T4's repair A: every "reduce an inferred type to a
shape" premise is now `DefEq μ Δ tx Shape`).

**The composition, once, in `inferShapeR`.**  Every one of these clauses
has the checker do

```
    t ← infer x ;  w ← whnf t ;  match w with | Shape => …
```

and every one of them now needs `∃ T', Infer Δ ⟦x⟧ T' ∧ DefEq Δ T' ⟦w⟧`.
The inference claim gives the first two thirds and the reduction claim
gives `Red Δ ⟦t⟧ ⟦w⟧`; `DefEq.trans` with `DefEq.ofRed` closes it.  That
single lemma is the whole content of the repair on the bridge side — it
is used four times here and will be used at every `Infer`+shape site of
batches (c)–(g).

Nothing else about these clauses changed from the shapes T2 wrote: the
premise *order* is the checker's, the abstraction round trip in I7 is
the same `abstract1_instantiate1` the TT lane needs, and I8/I10's
`denote_beta` moves are unchanged.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env}

/-! ## The composition lemma -/

/-- **A subject whose inferred type reduces to a shape infers a type
`DefEq` to that shape.**  The repair's whole bridge-side content: the
inference claim's slack composes with the reduction claim through
`DefEq.ofRed`.

Stated over `whnf` (the loop), which is what all four clauses call. -/
theorem inferShapeR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (ihw : WhnfClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {e t w : Expr}
    (hti : inferTypeCore mode env fuel d e = .ok t)
    (hw : whnf mode env fuel d t = .ok w)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOkR mode m.cval env φ d Δ e) :
    ∃ v W, denote m.cval env φ d e = some v ∧
      denote m.cval env φ d w = some W ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' W := by
  obtain ⟨v, tv, hv, htv, T', hI, hD⟩ := ihi hti hws hb hLb hC
  obtain ⟨htw, htb, htL, htC⟩ := frame_inferR m.wf hti hws hb hLb hC
  obtain ⟨W, hW, hR⟩ := ihw hw htw htb htL htC htv
  exact ⟨v, W, hv, hW, T', hI, hD.trans (DefEq.ofRed hR)⟩

/-- The same at a `.sort` shape, which is what `ensureSort` produces —
the form I6, I7 and I10 consume. -/
theorem inferSortR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (ihw : WhnfClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {e t : Expr} {u : Level}
    (hti : inferTypeCore mode env fuel d e = .ok t)
    (hw : whnf mode env fuel d t = .ok (.sort u))
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOkR mode m.cval env φ d Δ e)
    {v : VExpr} (hv : denote m.cval env φ d e = some v) :
    ∃ T', Infer mode env m.cval φ Δ v T' ∧
      DefEq mode env m.cval φ Δ T' (.sort (u.eval φ)) := by
  obtain ⟨v', W, hv', hW, T', hI, hD⟩ := inferShapeR m φ ihw ihi hti hw hws hb hLb hC
  obtain rfl : v' = v := by rw [hv'] at hv; exact Option.some.inj hv
  rw [denote_sort] at hW
  obtain rfl : W = .sort (u.eval φ) := (Option.some.inj hW).symm
  exact ⟨T', hI, hD⟩

/-! ## Frame conditions of an opened binder

The three binder clauses (I6, I7, and the `let`'s body) open with
`.fvar d n ty` and recurse at depth `d + 1`; their four frame
conditions are the same four every time. -/

/-- The frame conditions of a binder body opened with its own
variable. -/
theorem frame_openR {cval : TConstVal} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {n : Name} {ty body : Expr} {A : VExpr}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    (hwty : Expr.WScoped d ty) (hbty : ty.looseBVarsBounded 0 = true)
    (hwb : Expr.WScoped d body)
    (hbb : body.looseBVarsBounded 1 = true)
    (hLty : Expr.LeavesBounded ty) (hLbody : Expr.LeavesBounded body)
    (hCty : CtxOkR mode cval env φ d Δ ty)
    (hCbody : CtxOkR mode cval env φ d Δ body)
    (hA : denote cval env φ d ty = some A) :
    Expr.WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) ∧
      (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) ∧
      CtxOkR mode cval env φ (d + 1) (A :: Δ)
        (body.instantiate1 (.fvar d n ty)) := by
  refine ⟨Expr.WScoped.instantiate1 hwty 0 hwb,
    looseBVarsBounded_instantiate1 body 0 hbb, fun l hl => ?_,
    CtxOkR.open (n := n) hcl hCbody hCty hA hwty.fvarsBelow⟩
  rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
  · exact hLbody l h2
  · rw [Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hbty
    · exact hLty l h3

/-! ## I6: the `∀` clause -/

/-- `.forallE` infers by `Infer.pi`.  The one clause that opens a binder
on *both* sides of the rule (the domain's sort and the opened body's),
and so the one that consumes `CtxOkR.open` twice over. -/
theorem infer_forallE_claimR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {n : Name} {ty body t : Expr}
    {mb : BinderMeta}
    (h : inferTypeCore mode env (fuel + 1) d (.forallE n ty body mb) = .ok t)
    (hws : Expr.WScoped d (.forallE n ty body mb))
    (hb : (Expr.forallE n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.forallE n ty body mb))
    (hC : CtxOkR mode m.cval env φ d Δ (.forallE n ty body mb)) :
    ∃ v tv, denote m.cval env φ d (.forallE n ty body mb) = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv := by
  obtain ⟨tty, u, bt, vv, hty, hwu, hbt, hens, -, rfl⟩ :=
    inferTypeCore_forall_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCty : CtxOkR mode m.cval env φ d Δ ty :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCbody : CtxOkR mode m.cval env φ d Δ body :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  -- the domain is a type
  obtain ⟨A, vtty, hA, hvtty, TA, hAI, hAD⟩ := ihi hty hws.1 hb.1 hLty hCty
  have hAs : ∃ T', Infer mode env m.cval φ Δ A T' ∧
      DefEq mode env m.cval φ Δ T' (.sort (u.eval φ)) :=
    inferSortR m φ ihw ihi hty hwu hws.1 hb.1 hLty hCty hA
  obtain ⟨TA', hAI', hAD'⟩ := hAs
  -- open the binder and infer the codomain's sort
  obtain ⟨hwopen, hbopen, hLopen, hCopen⟩ :=
    frame_openR (n := n) hcl hws.1 hb.1 hws.2 hb.2 hLty hLbody hCty hCbody hA
  obtain ⟨B, vbt, hB, hvbt, TB, hBI, hBD⟩ := ihi hbt hwopen hbopen hLopen hCopen
  obtain ⟨TB', hBI', hBD'⟩ :=
    inferSortR m φ ihw ihi hbt (ensureSortCore_inv hens) hwopen hbopen hLopen
      hCopen hB
  refine ⟨.pi A B, .sort (Setlec.TT.imax (u.eval φ) (vv.eval φ)), ?_, ?_,
    _, Infer.pi hAI' hAD' hBI' hBD', DefEq.refl⟩
  · rw [denote_forallE, hA, hB]
  · rw [denote_sort]
    rfl

/-! ## I7: the `λ` clause

The checker infers the body's type in the opened context and then
*abstracts* it back under the binder, so the bridge undoes that round
trip: `denote` of `(bt.abstract1 d).instantiate1 (.fvar d n ty)` is
`denote` of `bt` (`abstract1_instantiate1`), provided every `fvar` at
index `d` in `bt` carries this binder's name and annotation — which the
leaf discipline gives, since the inferred type's leaves are a subset of
the opened body's and its only leaf at index `d` is the one the opening
inserted. -/

/-- Opening a λ-shaped body keeps it λ-shaped, and so does `denote`:
the task-#152 chain guard crosses from the checker's raw body to the
relation's denoted one. -/
private theorem denote_opened_isLam {cval : TConstVal} {env : Env}
    {φ : Name → Nat} {body x : Expr} {d : Nat} {v : VExpr}
    (hbl : body.isLam = true)
    (hden : denote cval env φ d (body.instantiate1 x) = some v) :
    v.isLam = true := by
  cases body <;> simp [Expr.isLam] at hbl
  next n ty b mb =>
    rw [show Expr.instantiate1 (.lam n ty b mb) x
        = .lam n (ty.instantiate1 x) (b.instantiate1 x 1) mb from rfl,
      denote_lam] at hden
    rcases h1 : denote cval env φ d (ty.instantiate1 x) with _ | A
    · rw [h1] at hden
      exact nomatch hden
    rw [h1] at hden
    rcases h2 : denote cval env φ (d + 1)
        (((b.instantiate1 x 1)).instantiate1
          (.fvar d n (ty.instantiate1 x))) with _ | bv
    · rw [h2] at hden
      exact nomatch hden
    rw [h2] at hden
    obtain rfl : v = .lam A bv := (Option.some.inj hden).symm
    rfl

/-- `.lam` infers by `Infer.lam`. -/
theorem infer_lam_claimR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {n : Name} {ty body t : Expr}
    {mb : BinderMeta}
    (h : inferTypeCore mode env (fuel + 1) d (.lam n ty body mb) = .ok t)
    (hws : Expr.WScoped d (.lam n ty body mb))
    (hb : (Expr.lam n ty body mb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.lam n ty body mb))
    (hC : CtxOkR mode m.cval env φ d Δ (.lam n ty body mb)) :
    ∃ v tv, denote m.cval env φ d (.lam n ty body mb) = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv := by
  obtain ⟨tty, u, bt, hty, hwu, hbt, h152, -, rfl⟩ :=
    inferTypeCore_lam_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCty : CtxOkR mode m.cval env φ d Δ ty :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCbody : CtxOkR mode m.cval env φ d Δ body :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  obtain ⟨A, vtty, hA, -, -, -, -⟩ := ihi hty hws.1 hb.1 hLty hCty
  obtain ⟨TA', hAI', hAD'⟩ :=
    inferSortR m φ ihw ihi hty hwu hws.1 hb.1 hLty hCty hA
  obtain ⟨hwopen, hbopen, hLopen, hCopen⟩ :=
    frame_openR (n := n) hcl hws.1 hb.1 hws.2 hb.2 hLty hLbody hCty hCbody hA
  obtain ⟨B, vbt, hB, hvbt, TB, hBI, hBD⟩ := ihi hbt hwopen hbopen hLopen hCopen
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
  -- the task-#152 codomain-sort premises (#151 tier C): live exactly
  -- when the checker ran the chain check
  have hlamI : Infer mode env m.cval φ Δ (.lam A B) (.pi A TB) := by
    by_cases hver : mode.verified = true
    · by_cases hbl : body.isLam = true
      · have hBlam : B.isLam = true := denote_opened_isLam hbl hB
        exact Infer.lam (B' := .sort 0) (tB := .sort 0) (v := 0)
          hAI' hAD' hBI
          (fun _ hnl => absurd hBlam (by rw [hnl]; exact Bool.noConfusion))
          (fun _ hnl => absurd hBlam (by rw [hnl]; exact Bool.noConfusion))
          (fun _ hnl => absurd hBlam (by rw [hnl]; exact Bool.noConfusion))
      · obtain ⟨btt, v', hbtt, hwv, -⟩ :=
          h152 hver (by simpa using hbl)
        have hwsbt : Expr.WScoped (d + 1) bt :=
          inferTypeCore_WScoped m.wf fuel hbt hwopen
        have hLbt : Expr.LeavesBounded bt := fun l hl =>
          hLopen l (inferTypeCore_fvarLeaves m.wf fuel hbt hwopen l hl)
        have hCbt : CtxOkR mode m.cval env φ (d + 1) (A :: Δ) bt :=
          CtxOkR.of_subset
            (fun l hl => inferTypeCore_fvarLeaves m.wf fuel hbt hwopen l hl)
            hCopen
        obtain ⟨tB', hIB', hDB'⟩ := inferSortR m φ ihw ihi hbtt hwv
          hwsbt hbtb hLbt hCbt hvbt
        exact Infer.lam hAI' hAD' hBI (fun _ _ => hBD)
          (fun _ _ => hIB') (fun _ _ => hDB')
    · exact Infer.lam (B' := .sort 0) (tB := .sort 0) (v := 0)
        hAI' hAD' hBI (fun hv _ => absurd hv hver)
        (fun hv _ => absurd hv hver) (fun hv _ => absurd hv hver)
  refine ⟨.lam A B, .pi A vbt, ?_, ?_, _, hlamI, ?_⟩
  · rw [denote_lam, hA, hB]
  · rw [denote_forallE, hA, hround, hvbt]
  · exact DefEq.piCong DefEq.refl hBD

/-! ## I8: the application clause

`Infer.app`'s four premises are the checker's four moves in order: the
head's inference, its reduction to a `∀` (now through the composed
`DefEq`), the argument's inference, and the per-argument re-check —
always on at `--set-model`. -/

/-- `.app` infers by `Infer.app`. -/
theorem infer_app_claimR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {f a t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.app f a) = .ok t)
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    (hC : CtxOkR mode m.cval env φ d Δ (.app f a)) :
    ∃ v tv, denote m.cval env φ d (.app f a) = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv := by
  obtain ⟨tf, n', ty', body', m', htf, hwf, rfl, ta, hta, hde⟩ :=
    inferTypeCore_app_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCf : CtxOkR mode m.cval env φ d Δ f :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCa : CtxOkR mode m.cval env φ d Δ a :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  -- the head, at a type `DefEq` to the ∀ the application names
  obtain ⟨vf, VPi, hvf, hVPi, TF, hFI, hFD⟩ :=
    inferShapeR m φ ihw ihi htf hwf hws.1 hb.1 hLf hCf
  rw [denote_forallE] at hVPi
  split at hVPi
  · exact nomatch hVPi
  · next A hA =>
    split at hVPi
    · exact nomatch hVPi
    · next B hB =>
      obtain rfl : VPi = .pi A B := (Option.some.inj hVPi).symm
      -- the argument, and the per-argument certificate
      obtain ⟨va, vta, hva, hvta, TAa, haI, haD⟩ := ihi hta hws.2 hb.2 hLa hCa
      obtain ⟨htaw, htab, htaL, htaC⟩ := frame_inferR m.wf hta hws.2 hb.2 hLa hCa
      -- the ∀'s own frame conditions, for the domain certificate
      have hwfe : Expr.WScoped d (Expr.forallE n' ty' body' m') := by
        obtain ⟨htfw, -, -, -⟩ := frame_inferR m.wf htf hws.1 hb.1 hLf hCf
        exact whnf_WScoped m.wf fuel hwf htfw
      have hbfe : (Expr.forallE n' ty' body' m').looseBVarsBounded 0 = true := by
        obtain ⟨-, htfb, -, -⟩ := frame_inferR m.wf htf hws.1 hb.1 hLf hCf
        exact whnf_looseBVars m.wf fuel hwf htfb
      have hLfe : Expr.LeavesBounded (.forallE n' ty' body' m') := by
        obtain ⟨-, -, htfL, -⟩ := frame_inferR m.wf htf hws.1 hb.1 hLf hCf
        exact fun l hl => htfL l (whnf_fvarLeaves m.wf fuel hwf l hl)
      have hCfe : CtxOkR mode m.cval env φ d Δ (.forallE n' ty' body' m') := by
        obtain ⟨-, -, -, htfC⟩ := frame_inferR m.wf htf hws.1 hb.1 hLf hCf
        exact CtxOkR.of_subset (whnf_fvarLeaves m.wf fuel hwf) htfC
      simp only [Expr.WScoped] at hwfe
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
      have hLty : Expr.LeavesBounded ty' := fun l hl =>
        hLfe l (by simp [Expr.fvarLeaves, hl])
      have hCty : CtxOkR mode m.cval env φ d Δ ty' :=
        CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCfe
      have hDdom : DefEq mode env m.cval φ Δ vta A :=
        ihd hde htaw htab htaL hwfe.1 hbfe.1 hLty htaC hCty hvta hA
      refine ⟨.app vf va, VExpr.inst B va, ?_, ?_,
        _, Infer.app hFI hFD haI (haD.trans hDdom), DefEq.refl⟩
      · rw [denote_app, hvf, hva]
      · rw [denote_beta (n := n') (ty := ty') hcl hwfe.2.fvarsBelow hws.2
          hb.2 hva 0, hB]
        rfl

/-! ## I10: the `let` clause

`Infer.letE` takes five premises and the checker supplies all five in
order: the annotation's inference and sort, the value's inference and
its certificate against the annotation, and the body's inference **on
the substituted body** — which is what the rule types, so no opening is
needed on either side. -/

/-- `.letE` infers by `Infer.letE`. -/
theorem infer_letE_claimR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {n : Name} {ty val b t : Expr}
    (h : inferTypeCore mode env (fuel + 1) d (.letE n ty val b) = .ok t)
    (hws : Expr.WScoped d (.letE n ty val b))
    (hb : (Expr.letE n ty val b).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE n ty val b))
    (hC : CtxOkR mode m.cval env φ d Δ (.letE n ty val b)) :
    ∃ v tv, denote m.cval env φ d (.letE n ty val b) = some v ∧
      denote m.cval env φ d t = some tv ∧
      ∃ T', Infer mode env m.cval φ Δ v T' ∧
        DefEq mode env m.cval φ Δ T' tv := by
  obtain ⟨tty, s, tv, hty, hens, hvv, hde, hbody⟩ := inferTypeCore_letE_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLval : Expr.LeavesBounded val := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCty : CtxOkR mode m.cval env φ d Δ ty :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  have hCval : CtxOkR mode m.cval env φ d Δ val :=
    CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC
  -- premise one and two: the annotation is a type
  obtain ⟨A, vtty, hA, hvtty, TA, hAI, hAD⟩ := ihi hty hws.1 hb.1.1 hLty hCty
  obtain ⟨TA', hAI', hAD'⟩ :=
    inferSortR m φ ihw ihi hty (ensureSortCore_inv hens) hws.1 hb.1.1 hLty
      hCty hA
  -- premise three and four: the value is at the annotation
  obtain ⟨xv, vtv, hxv, hvtv, TV, hVI, hVD⟩ := ihi hvv hws.2.1 hb.1.2 hLval hCval
  obtain ⟨htvw, htvb, htvL, htvC⟩ := frame_inferR m.wf hvv hws.2.1 hb.1.2 hLval hCval
  have hVA : DefEq mode env m.cval φ Δ TV A :=
    hVD.trans (ihd hde htvw htvb htvL hws.1 hb.1.1 hLty htvC hCty hvtv hA)
  -- premise five: the substituted body, which is what the rule types
  have hwred : Expr.WScoped d (b.instantiate1 val) :=
    Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
  have hbred : (b.instantiate1 val).looseBVarsBounded 0 = true :=
    Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
  have hLred : Expr.LeavesBounded (b.instantiate1 val) := fun l hl => by
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · exact hLb l (by simp [Expr.fvarLeaves, h2])
    · exact hLval l h2
  have hCred : CtxOkR mode m.cval env φ d Δ (b.instantiate1 val) := by
    refine ⟨hC.1, fun l hl => ?_⟩
    rcases Expr.fvarLeaves_instantiate1 b 0 hl with h2 | h2
    · exact hC.2 l (by simp [Expr.fvarLeaves, h2])
    · exact hCval.2 l h2
  obtain ⟨bv, btv, hbv, hbtv, TB, hBI, hBD⟩ := ihi hbody hwred hbred hLred hCred
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
  refine ⟨.letE A xv B, btv, ?_, hbtv,
    _, Infer.letE hAI' hAD' hVI hVA hBI, hBD⟩
  rw [denote_letE, hA, hxv, hB]

/-! ## The four obligations, discharged -/

/-- **`InferPiStepR`, proved.** -/
theorem inferPi_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel) :
    InferPiStepR (mode := mode) m φ fuel := fun h hws hb hLb hC =>
  infer_forallE_claimR m φ hcl ihw ihi h hws hb hLb hC

/-- **`InferLamStepR`, proved.** -/
theorem inferLam_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel) :
    InferLamStepR (mode := mode) m φ fuel := fun h hws hb hLb hC =>
  infer_lam_claimR m φ hcl ihw ihi h hws hb hLb hC

/-- **`InferAppStepR`, proved.** -/
theorem inferApp_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel) :
    InferAppStepR (mode := mode) m φ fuel := fun h hws hb hLb hC =>
  infer_app_claimR m φ hcl ihw ihd ihi h hws hb hLb hC

/-- **`InferLetStepR`, proved.** -/
theorem inferLet_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel) :
    InferLetStepR (mode := mode) m φ fuel := fun h hws hb hLb hC =>
  infer_letE_claimR m φ hcl ihw ihd ihi h hws hb hLb hC

end Setlec.SetR
