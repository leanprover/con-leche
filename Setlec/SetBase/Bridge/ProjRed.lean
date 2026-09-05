import Setlec.SetBase.Bridge.Proj

/-!
# `ProjStepR`, discharged (task #148, T3, batch e)

R6 `Red.projRed`, the scrutinee's reduction (R7 at the `.proj` site),
and the stuck branch — which is **`Red.projArg`**, finding 2's rule, and
this is the site that shows why it had to exist: *every* non-firing
branch of `whnfCoreBody`'s `.proj` clause returns the reduced scrutinee
under the projection.

## The walk, general rather than concrete

The R6 amendment exposed the constructor spine's telescope as a premise
and the verification (`Setlec/SetR/DESIGN.md`) established that it comes
from inverting the `inferTypeCore` run `projCert` performs.  The model
does that walk **concretely**, four `inferTypeCore_app_inv'` steps down
the pinned `PSigma'.mk` type with each domain computed by hand.  The
bridge does it **generically**, in `tele_of_inferSpineR`:

* `inferTypeCore_app_inv'` peels one argument at a time (right to left,
  which is how an application chain is built), each step yielding
  `infer arg` and `defeq ta dom` — `Tele.cons`'s premise pair, in the
  checker's own order;
* the alignment between the walk's `whnf`'d domains and `Tele`'s
  *syntactic* peeling is `whnf_forallE_self`: a `∀`-tower is its own
  whnf.  The tower witness is `stripPis`, which the checker's own
  install guards already pin, and which survives instantiation
  (`stripPis_instantiate1`) — so the invariant carries down the walk;
* `Tele.snoc` puts the steps together, since the peeling runs right to
  left while `Tele` is built left to right.

Doing it generically rather than concretely costs nothing here and pays
in batch (g): R11's recursor and constructor telescopes are the same
walk at a different arity, and neither of those types is pinned.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify
variable {mode : CheckMode} {env : Env}

/-- `stripPis` is monotone downwards. -/
theorem stripPis_mono : ∀ (k : Nat) {E : Expr},
    (E.stripPis (k + 1)).isSome = true → (E.stripPis k).isSome = true := by
  intro k
  induction k with
  | zero => intro E _; rfl
  | succ k ih =>
    intro E h
    match E, h with
    | .forallE n ty b mb, h =>
      simp only [Expr.stripPis, Option.isSome_map] at h ⊢
      exact ih h

/-- `stripPis` is monotone downwards, at any gap. -/
theorem stripPis_le : ∀ {k n : Nat}, k ≤ n → ∀ {E : Expr},
    (E.stripPis n).isSome = true → (E.stripPis k).isSome = true := by
  intro k n
  induction n with
  | zero => intro h E hE; obtain rfl : k = 0 := Nat.le_zero.mp h; exact hE
  | succ n ih =>
    intro h E hE
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · exact ih (by omega) (stripPis_mono n hE)
    · obtain rfl : k = n + 1 := by omega
      exact hE

/-- A syntactic `∀`-tower survives instantiation: `instantiate1` maps
`forallE` to `forallE`, hereditarily. -/
theorem stripPis_instantiate1 : ∀ (k : Nat) {b : Expr} (a : Expr) (j : Nat),
    (b.stripPis k).isSome = true →
    ((b.instantiate1 a j).stripPis k).isSome = true := by
  intro k
  induction k with
  | zero => intro b a j _; rfl
  | succ k ih =>
    intro b a j h
    match b, h with
    | .forallE n ty bd mb, h =>
      simp only [Expr.stripPis, Option.isSome_map] at h ⊢
      rw [show (Expr.forallE n ty bd mb).instantiate1 a j
        = Expr.forallE n (ty.instantiate1 a j) (bd.instantiate1 a (j + 1)) mb
        from rfl]
      simp only [Expr.stripPis, Option.isSome_map]
      exact ih _ _ h

/-- A `∀`-tower is its own whnf, so a `whnf` that lands on a `forallE`
lands on the tower itself. -/
theorem whnf_forallE_self {fuel d : Nat} {E e' : Expr}
    (hs : (E.stripPis 1).isSome = true)
    (h : whnf mode env fuel d E = .ok e') : e' = E := by
  match E, hs with
  | .forallE n ty b mb, _ => exact whnf_forallE_eq h

/-- The spine's run reaches the head's: `inferTypeCore` on an
application chain computes the head's type on the way down. -/
theorem inferSpine_headR {env : Env} {fuel d : Nat} {f : Expr} :
    ∀ (rs : List Expr) {t : Expr},
      inferTypeCore mode env fuel d (Expr.mkAppN f rs.reverse) = .ok t →
      ∃ tf₀, inferTypeCore mode env fuel d f = .ok tf₀ := by
  intro rs
  induction rs with
  | nil => intro t h; exact ⟨t, h⟩
  | cons a rs' ih =>
    intro t h
    rw [List.reverse_cons, Expr.mkAppN_append_one] at h
    obtain ⟨tf, -, -, -, -, htf, -⟩ := inferTypeCore_app_inv' h
    exact ih htf

/-- `Tele` extends on the right: a walk that ends at a `∀` takes one
more argument.  (The family is mutually inductive, so the induction is
on the spine, not on the derivation.) -/
theorem Tele.snoc {cval : TConstVal} {φ : Name → Nat} {Δ : List VExpr}
    {A B a ta : VExpr} :
    ∀ {T : VExpr} {as : List VExpr},
      Tele mode env cval φ Δ T as (.pi A B) →
      Infer mode env cval φ Δ a ta → DefEq mode env cval φ Δ ta A →
      Tele mode env cval φ Δ T (as ++ [a]) (B.inst a) := by
  intro T as
  induction as generalizing T with
  | nil =>
    intro h hI hD
    cases h
    exact Tele.cons hI hD Tele.nil
  | cons x xs ih =>
    intro h hI hD
    cases h with | cons hI' hD' htail => ?_
    exact Tele.cons hI' hD' (ih htail hI hD)

/-- **A certified application spine is a `Tele`, walked through the
infer run.**  The R6 amendment's premise, from the checker's own
`inferTypeCore` on the constructor application: `inferTypeCore_app_inv'`
peels one argument at a time, each step yielding `infer arg` and
`defeq ta dom` — `Tele.cons`'s pair — and `whnf_forallE_self` says the
partial application's inferred type, being a `∀`-tower residual, is its
own whnf, which is what aligns the walk's domains with `Tele`'s
syntactic peeling.

The `stripPis` hypothesis is the tower witness; it is exactly the guard
the checker's own install pins (`(cvj.type.stripPis n).isSome`). -/
theorem tele_of_inferSpineR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {f : Expr} {tf₀ : Expr} {TF : VExpr}
    (hf₀ : inferTypeCore mode env fuel d f = .ok tf₀)
    (hTF : denote m.cval env φ d tf₀ = some TF)
    (hwf : Expr.WScoped d f) (hbf : f.looseBVarsBounded 0 = true)
    (hLf : Expr.LeavesBounded f) (hCf : CtxOkR mode m.cval env φ d Δ f) :
    ∀ (rs : List Expr) {t : Expr} {vs : List VExpr} (k : Nat),
      inferTypeCore mode env fuel d (Expr.mkAppN f rs.reverse) = .ok t →
      (tf₀.stripPis (rs.length + k)).isSome = true →
      DenoteSpine m.cval env φ d rs.reverse vs →
      (∀ x ∈ rs, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkR mode m.cval env φ d Δ x) →
      ∃ rest, denote m.cval env φ d t = some rest ∧
        (t.stripPis k).isSome = true ∧
        Tele mode env m.cval φ Δ TF vs rest := by
  intro rs
  induction rs with
  | nil =>
    intro t vs k h hstrip hsp _
    cases hsp
    rw [show Expr.mkAppN f ([] : List Expr).reverse = f from rfl] at h
    rw [hf₀] at h
    obtain rfl : t = tf₀ := (Except.ok.inj h).symm
    exact ⟨TF, hTF, by simpa using hstrip, Tele.nil⟩
  | cons a rs' ih =>
    intro t vs k h hstrip hsp hfr
    rw [List.reverse_cons] at hsp
    rw [List.reverse_cons, Expr.mkAppN_append_one] at h
    obtain ⟨vs', va, rfl, hsp', hva⟩ := DenoteSpine.snoc_inv hsp
    obtain ⟨tf, n', ty', body', m', htf, hwtf, rfl, ta, hta, hde⟩ :=
      inferTypeCore_app_inv' h
    obtain ⟨hwa, hba, hLa, hCa⟩ := hfr a (by simp)
    obtain ⟨mid, hmid, hmids, htele⟩ :=
      ih (k := k + 1) htf
        (by rw [show rs'.length + (k + 1) = (a :: rs').length + k from by
              simp; omega]
            exact hstrip)
        hsp' (fun x hx => hfr x (by simp [hx]))
    -- the partial application's inferred type is a `∀`-tower residual,
    -- hence its own whnf
    have htfs : (tf.stripPis 1).isSome = true :=
      stripPis_le (k := 1) (n := k + 1) (by omega) hmids
    have heqtf := whnf_forallE_self htfs hwtf
    subst heqtf
    rw [denote_forallE] at hmid
    split at hmid
    · exact nomatch hmid
    · next A hA =>
      split at hmid
      · exact nomatch hmid
      · next B hB =>
        obtain rfl : mid = .pi A B := (Option.some.inj hmid).symm
        obtain ⟨x, tv, hix, hita, TX, hXI, hXD⟩ := ihi hta hwa hba hLa hCa
        have hxva : x = va := by rw [hix] at hva; exact Option.some.inj hva
        rw [← hxva]
        obtain ⟨hwta, hbta, hLta, hCta⟩ :=
          frame_inferR m.wf hta hwa hba hLa hCa
        -- the ∀'s own frames, for the domain certificate
        have hwT : Expr.WScoped d (Expr.forallE n' ty' body' m') := by
          have := inferTypeCore_WScoped m.wf fuel htf
            (Expr.WScoped.mkAppN hwf (fun y hy => (hfr y (List.mem_cons_of_mem a (List.mem_reverse.mp hy))).1))
          exact this
        have hbT : (Expr.forallE n' ty' body' m').looseBVarsBounded 0 = true := by
          exact inferTypeCore_looseBVars m.wf fuel htf
            (Expr.WScoped.mkAppN hwf (fun y hy => (hfr y (List.mem_cons_of_mem a (List.mem_reverse.mp hy))).1))
            (looseBVarsBounded_mkAppN hbf (fun y hy => (hfr y (List.mem_cons_of_mem a (List.mem_reverse.mp hy))).2.1))
            (fun l hl => by
              rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
              · exact hLf l hl'
              · exact (hfr y (List.mem_cons_of_mem a (List.mem_reverse.mp hy))).2.2.1 l hly)
        have hLT : Expr.LeavesBounded (Expr.forallE n' ty' body' m') := by
          intro l hl
          refine (fun l hl => ?_ : Expr.LeavesBounded (Expr.mkAppN f rs'.reverse)) l
            (inferTypeCore_fvarLeaves m.wf fuel htf
              (Expr.WScoped.mkAppN hwf (fun y hy => (hfr y (List.mem_cons_of_mem a (List.mem_reverse.mp hy))).1)) l hl)
          rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
          · exact hLf l hl'
          · exact (hfr y (List.mem_cons_of_mem a (List.mem_reverse.mp hy))).2.2.1 l hly
        have hCT : CtxOkR mode m.cval env φ d Δ (Expr.forallE n' ty' body' m') := by
          refine CtxOkR.of_subset (inferTypeCore_fvarLeaves m.wf fuel htf
            (Expr.WScoped.mkAppN hwf (fun y hy => (hfr y (List.mem_cons_of_mem a (List.mem_reverse.mp hy))).1))) ?_
          refine ⟨hCf.1, fun l hl => ?_⟩
          rcases fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
          · exact hCf.2 l hl'
          · exact (hfr y (List.mem_cons_of_mem a (List.mem_reverse.mp hy))).2.2.2.2 l hly
        simp only [Expr.WScoped] at hwT
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbT
        have hDdom : DefEq mode env m.cval φ Δ tv A :=
          ihd hde hwta hbta hLta hwT.1 hbT.1
            (fun l hl => hLT l (by simp [Expr.fvarLeaves, hl]))
            hCta (CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCT)
            hita hA
        refine ⟨VExpr.inst B x, ?_, ?_, Tele.snoc htele hXI (hXD.trans hDdom)⟩
        · rw [denote_beta (n := n') (ty := ty') hcl hwT.2.fvarsBelow hwa hba
            hix 0, hB]
          rfl
        · have : ((Expr.forallE n' ty' body' m').stripPis (k + 1)).isSome = true :=
            hmids
          simp only [Expr.stripPis, Option.isSome_map] at this
          exact stripPis_instantiate1 k a 0 this

/-! ## The scrutinee's reduction

`whnfCoreBody`'s `.proj` clause reduces the scrutinee with `whnf` and
then expands a string literal (`projLitToCtor`) before consulting the
table.  Both moves are reductions of the denotation: the first by the
loop claim, the second by R7 — whose two `denoteClosed` side conditions
are `denote_strLitCtorR`. -/

/-- The scrutinee, reduced and literal-expanded. -/
theorem proj_scrutineeR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel)
    {d : Nat} {Δ : List VExpr} {pe e₂ e₃ : Expr} {vp : VExpr}
    (hwpe : whnf mode env fuel d pe = .ok e₂)
    (hlit : projLitToCtorP mode env fuel d e₂ = .ok e₃)
    (hws : Expr.WScoped d pe) (hb : pe.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded pe) (hC : CtxOkR mode m.cval env φ d Δ pe)
    (hvp : denote m.cval env φ d pe = some vp) :
    ∃ v₃, denote m.cval env φ d e₃ = some v₃ ∧
      Red mode env m.cval φ Δ vp v₃ ∧
      Expr.WScoped d e₃ ∧ e₃.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₃ ∧ CtxOkR mode m.cval env φ d Δ e₃ := by
  obtain ⟨v₂, hv₂, hR₂, hw₂, hb₂, hL₂, hC₂⟩ :=
    whnf_packageR m φ ihw hwpe hws hb hLb hC hvp
  rcases projLitToCtorP_inv hlit with rfl | ⟨s, rfl, hg, hred⟩
  · exact ⟨v₂, hv₂, hR₂, hw₂, hb₂, hL₂, hC₂⟩
  · -- the string-literal expansion: R7, then the loop claim on the
    -- (closed) constructor form
    obtain ⟨hSC0, hSCc, hSCd⟩ := denote_strLitCtorR m φ hcl hg d s
    obtain ⟨hwc, hbc, hLc, hCc⟩ :=
      frame_strLitCtorR (mode := mode) (cval := m.cval) (φ := φ) s hC.1
    obtain ⟨v₃, hv₃, hR₃, hw₃, hb₃, hL₃, hC₃⟩ :=
      whnf_packageR m φ ihw hred hwc hbc hLc hCc hSCd
    rw [denote_strLit, if_pos hg] at hv₂
    obtain rfl : v₂ = strLitT m.cval env φ s := (Option.some.inj hv₂).symm
    exact ⟨v₃, hv₃, hR₂.trans (Red.strLitCtor hg hSC0 hSCc hR₃),
      hw₃, hb₃, hL₃, hC₃⟩

/-- The pinned constructor's type, denoted at any depth, closed, and a
4-ary `∀`-tower. -/
theorem denote_ctorTyR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hpsig : env.find? psigmaName = some psigmaA) (l0 l1 : Level) :
    ∃ TC, denoteClosed m.cval env φ
        (psigmaMkA.toConstantVal.type.instantiateLevelParams
          psigmaMkA.toConstantVal.levelParams [l0, l1]) = some TC ∧
      VExpr.Closed TC ∧
      ∀ D, denote m.cval env φ D
        (psigmaMkA.toConstantVal.type.instantiateLevelParams
          psigmaMkA.toConstantVal.levelParams [l0, l1]) = some TC := by
  obtain ⟨hc, hd⟩ := denote_closedExprR hcl (by rfl) (by rfl)
    (denote_psigmaMkTy_eq (cval := m.cval) (φ := φ) hpsig l0 l1)
  exact ⟨_, denote_psigmaMkTy_eq hpsig l0 l1, hc, hd⟩

/-- **`ProjStepR`, proved** (R6/R6′, and R7 at the scrutinee).  The
stuck branch is `Red.projArg` — finding 2's rule, and the reason it
had to exist: *every* non-firing branch of the clause returns the
reduced scrutinee under the projection — iterated along `projNV` at a
tower-backed entry (`Red.projNV_arg`).  The firing branch at a
tower-backed entry (task #175 wiring W5) is R6′ with the constructor's
stored type in place of the pinned one. -/
theorem proj_stepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hg : mode.betaGate = false)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsR mode m φ fuel) (ihw : WhnfClaimsR mode m φ fuel)
    (ihd : DefEqClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel) :
    ProjStepR (mode := mode) m φ fuel := by
  intro d Δ sn i pe e' v h hws hb hLb hC hv
  obtain ⟨e₂, e₃, hwpe, hlit, hcase⟩ := whnf_proj_inv h
  rw [denote_proj] at hv
  cases hvp : denote m.cval env φ d pe with
  | none => rw [hvp] at hv; exact nomatch hv
  | some vp =>
  rw [hvp] at hv
  dsimp only at hv
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOkR mode m.cval env φ d Δ pe :=
    CtxOkR.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl) hC
  obtain ⟨v₃, hv₃, hR₃, hw₃, hb₃, hL₃, hC₃⟩ :=
    proj_scrutineeR m φ hcl ihw hwpe hlit hws hb hLpe hCpe hvp
  -- the reading of the stuck node at the reduced scrutinee, at either
  -- entry kind
  have hstuck : ∀ (v' : VExpr), v = v' →
      (∀ entry, env.findProj? sn i = some entry → entry.tower = true →
        v' = projNV i vp) →
      ((∀ entry, env.findProj? sn i = some entry → entry.tower = false) →
        i < 2 → v' = .proj i vp) →
      ∃ w, denote m.cval env φ d (.proj sn i e₃) = some w ∧
        Red mode env m.cval φ Δ v' w := by
    intro v' hvv htw hpr
    rw [denote_proj, hv₃]
    dsimp only
    cases hfp : env.findProj? sn i with
    | some entry =>
      rw [hfp] at hv
      dsimp only at hv ⊢
      by_cases htwe : entry.tower = true
      · rw [if_pos htwe] at hv ⊢
        rw [htw entry hfp htwe]
        exact ⟨_, rfl, Red.projNV_arg hR₃⟩
      · rw [if_neg htwe] at hv ⊢
        have htwf : entry.tower = false := by
          cases hh : entry.tower
          · rfl
          · exact absurd hh htwe
        by_cases hi2 : i < 2
        · rw [if_pos hi2] at hv ⊢
          rw [hpr (fun e he => by
            obtain rfl : entry = e := Option.some.inj (hfp.symm.trans he)
            exact htwf) hi2]
          exact ⟨_, rfl, Red.projArg hR₃⟩
        · rw [if_neg hi2] at hv; exact nomatch hv
    | none =>
      rw [hfp] at hv
      dsimp only at hv ⊢
      by_cases hi2 : i < 2
      · rw [if_pos hi2] at hv ⊢
        rw [hpr (fun e he => by rw [hfp] at he; exact nomatch he) hi2]
        exact ⟨_, rfl, Red.projArg hR₃⟩
      · rw [if_neg hi2] at hv; exact nomatch hv
  rcases hcase with rfl |
    ⟨us, entry, hfn, hfe, hnat, hilt, hlenA, hlenU, hfire, hwcf, hcert⟩
  · -- stuck: the reduced scrutinee under the projection
    refine hstuck v rfl ?_ ?_
    · intro entry hfp htwe
      rw [hfp] at hv; dsimp only at hv; rw [if_pos htwe] at hv
      exact (Option.some.inj hv).symm
    · intro hnt hi2
      cases hfp : env.findProj? sn i with
      | some entry =>
        rw [hfp] at hv; dsimp only at hv
        rw [if_neg (by simp [hnt entry hfp]), if_pos hi2] at hv
        exact (Option.some.inj hv).symm
      | none =>
        rw [hfp] at hv; dsimp only at hv; rw [if_pos hi2] at hv
        exact (Option.some.inj hv).symm
  · -- the table fires
    rw [hfe] at hv
    dsimp only at hv
    -- the constructor spine, denoted
    rw [show e₃ = Expr.mkAppN e₃.getAppFn e₃.getAppArgs from
      (Expr.mkAppN_getApp e₃).symm, hfn] at hv₃
    obtain ⟨vc, vs, hvc, hspa, rfl⟩ := denote_mkAppN_inv hv₃
    -- the certificate pack
    obtain ⟨ta, te, hita, hite⟩ := projCert_inv hcert
    rw [Setlec.inferTypeIO_off hg] at hita hite
    -- frames for the spine and for the projected field
    have hfrE : ∀ x ∈ e₃.getAppArgs, Expr.WScoped d x ∧
        x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
        CtxOkR mode m.cval env φ d Δ x :=
      frame_spineR hw₃ hb₃ hL₃ hC₃
    have hmem : e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0)
        ∈ e₃.getAppArgs :=
      getD_mem (by rw [hlenA]; omega)
    obtain ⟨hwF, hbF, hLF, hCF⟩ := hfrE _ hmem
    have hidx' : (entry.numParams + i) < vs.length := by
      rw [hspa.length, hlenA]; omega
    have hfvd : denote m.cval env φ d
        (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0))
        = some (vs.getD (entry.numParams + i) default) := by
      have := hspa.get ⟨entry.numParams + i, by rw [hspa.length] at hidx'; exact hidx'⟩
      simpa [List.getD, List.getElem?_eq_getElem
        (show entry.numParams + i < e₃.getAppArgs.length by
          rw [hlenA]; omega)] using this
    have hE₃ : Expr.mkAppN (Expr.const entry.ctor us) e₃.getAppArgs = e₃ := by
      rw [← hfn]; exact Expr.mkAppN_getApp e₃
    -- the head's own infer run
    obtain ⟨tf₀, hf₀⟩ :=
      inferSpine_headR (f := Expr.const entry.ctor us)
        e₃.getAppArgs.reverse (by
          rw [List.reverse_reverse, hE₃]
          exact hite)
    obtain ⟨ciMk, hfMk, -, rfl⟩ := inferTypeCore_const_inv hf₀
    -- the two certificate chains, shared by both entry kinds
    obtain ⟨fv, vta, hfv, hvta, T₁, hI₁, hD₁⟩ := ihi hita hwF hbF hLF hCF
    obtain rfl : fv = vs.getD (entry.numParams + i) default := by
      rw [hfv] at hfvd; exact Option.some.inj hfvd
    obtain ⟨vP, vte, hvP, hvte, S₁, hJ₁, hE₁⟩ := ihi hite hw₃ hb₃ hL₃ hC₃
    rw [← hE₃] at hvP
    -- the field's own head normalization
    obtain ⟨w, hw, hRw⟩ := ihwc hwcf hwF hbF hLF hCF hfvd
    by_cases htw : entry.tower = true
    · -- TOWER-BACKED (task #175 wiring W5): R6′ at the stored constructor
      rw [if_pos htw] at hv
      obtain rfl : v = projNV i vp := (Option.some.inj hv).symm
      obtain ⟨-, -, -, -, -, -, ⟨cvC, hfC, hlpsC, hstrip⟩, -⟩ :=
        m.proj_ok.towerHead hfe htw
      obtain rfl : ciMk = .ctorInfo cvC entry.numParams entry.numFields :=
        Option.some.inj (hfMk.symm.trans hfC)
      have hlenC : us.length = (ConstantInfo.ctorInfo cvC entry.numParams
          entry.numFields).toConstantVal.levelParams.length := by
        show us.length = cvC.levelParams.length
        rw [hlpsC]; exact hlenU
      rw [denote_const, hfC] at hvc
      dsimp only at hvc
      rw [if_pos hlenC] at hvc
      obtain rfl : vc = m.cval entry.ctor (Level.substFn φ
          (ConstantInfo.ctorInfo cvC entry.numParams
            entry.numFields).toConstantVal.levelParams us) :=
        (Option.some.inj hvc).symm
      -- the constructor's stored type: denoted, closed, depth-free
      have hmemC := find?_mem hfC
      obtain ⟨TC, hTC'⟩ := m.ty_denotes _ hmemC (Level.substFn φ
        (ConstantInfo.ctorInfo cvC entry.numParams
          entry.numFields).toConstantVal.levelParams us)
      obtain ⟨hnfC, -, -, hbdC, -⟩ := m.wf _ hmemC
      have hTC0 : denoteClosed m.cval env φ
          ((ConstantInfo.ctorInfo cvC entry.numParams
            entry.numFields).toConstantVal.type.instantiateLevelParams
            (ConstantInfo.ctorInfo cvC entry.numParams
              entry.numFields).toConstantVal.levelParams us) = some TC := by
        rw [denoteClosed, denote_instLevels m.val_params]
        exact hTC'
      have hnfC' : ((ConstantInfo.ctorInfo cvC entry.numParams
          entry.numFields).toConstantVal.type.instantiateLevelParams
          (ConstantInfo.ctorInfo cvC entry.numParams
            entry.numFields).toConstantVal.levelParams us).hasFvar = false := by
        rw [Expr.hasFvar_instantiateLevelParams]; exact hnfC
      have hbdC' : ((ConstantInfo.ctorInfo cvC entry.numParams
          entry.numFields).toConstantVal.type.instantiateLevelParams
          (ConstantInfo.ctorInfo cvC entry.numParams
            entry.numFields).toConstantVal.levelParams us).looseBVarsBounded 0
          = true := by
        rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hbdC
      obtain ⟨hTCc, hTCd⟩ := denote_closedExprR hcl hnfC' hbdC' hTC0
      -- the constructor spine's telescope: the infer run's own
      -- per-argument re-checks, walked (the R6 amendment)
      obtain ⟨rest, hrest, -, htele⟩ :=
        tele_of_inferSpineR m φ hcl ihd ihi hf₀ (hTCd d)
          (Expr.WScoped.of_not_hasFvar rfl) rfl
          (Expr.LeavesBounded.of_not_hasFvar rfl)
          (CtxOkR.of_fvarLeaves_nil hC.1 (by simp [Expr.fvarLeaves]))
          e₃.getAppArgs.reverse (k := 0)
          (by rw [List.reverse_reverse, hE₃]; exact hite)
          (by rw [List.length_reverse, hlenA, Nat.add_zero]
              exact Setlec.Expr.stripPis_instantiateLevelParams_isSome _ _ _ hstrip)
          (by rw [List.reverse_reverse]; exact hspa)
          (fun x hx => hfrE x (List.mem_reverse.mp hx))
      obtain rfl : vP = VExpr.mkAppN (m.cval entry.ctor (Level.substFn φ
          (ConstantInfo.ctorInfo cvC entry.numParams
            entry.numFields).toConstantVal.levelParams us)) vs := by
        rw [hvP] at hv₃
        exact Option.some.inj hv₃
      refine ⟨w, hw, Red.trans ?_ hRw⟩
      refine Red.projRedTower hfe hnat htw hilt (by rw [hspa.length, hlenA])
        hlenU hfire hfC hlenC rfl ?_ hTC0 hTCc hR₃ htele hI₁ hD₁ hJ₁ hE₁
      simp only [List.getD, List.getElem?_eq_getElem hidx']
      rfl
    · -- PAIR-BACKED: the pinned constructor, as before
      rw [if_neg htw] at hv
      have htw' : entry.tower = false := by
        cases hh : entry.tower
        · rfl
        · exact absurd hh htw
      obtain ⟨hpin, rfl, hidx, hpsig, hpsigMk⟩ :=
        projEntry_pins m.proj_ok hfe hnat htw'
      have hi2 : i < 2 := by
        rcases hpin with rfl | rfl <;> · rw [← hidx]; simp [pairFstEntry, pairSndEntry]
      rw [if_pos hi2] at hv
      obtain rfl : v = .proj i vp := (Option.some.inj hv).symm
      have hctor : entry.ctor = psigmaMkName := by
        rcases hpin with rfl | rfl <;> rfl
      have hlen2 : us.length = 2 := by
        rcases hpin with rfl | rfl <;> simpa [pairFstEntry, pairSndEntry] using hlenU
      obtain ⟨l0, l1, rfl⟩ := List.length_two' hlen2
      have hfctor : env.find? entry.ctor = some psigmaMkA := by
        rw [hctor]; exact hpsigMk
      rw [denote_const, hfctor] at hvc
      dsimp only at hvc
      split at hvc
      · next hlenC =>
        obtain rfl : vc = m.cval entry.ctor
            (Level.substFn φ psigmaMkA.toConstantVal.levelParams [l0, l1]) :=
          (Option.some.inj hvc).symm
        obtain ⟨TC, hTC0, hTCc, hTCd⟩ := denote_ctorTyR m φ hcl hpsig l0 l1
        obtain rfl : ciMk = psigmaMkA := by
          rw [hfMk] at hfctor; exact Option.some.inj hfctor
        obtain ⟨rest, hrest, -, htele⟩ :=
          tele_of_inferSpineR m φ hcl ihd ihi hf₀ (hTCd d)
            (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl)
            (CtxOkR.of_fvarLeaves_nil hC.1 (by simp [Expr.fvarLeaves]))
            e₃.getAppArgs.reverse (k := 0)
            (by rw [List.reverse_reverse, hE₃]; exact hite)
            (by rw [List.length_reverse, hlenA]
                rcases hpin with rfl | rfl <;> rfl)
            (by rw [List.reverse_reverse]; exact hspa)
            (fun x hx => hfrE x (List.mem_reverse.mp hx))
        obtain rfl : vP = VExpr.mkAppN (m.cval entry.ctor
            (Level.substFn φ psigmaMkA.toConstantVal.levelParams [l0, l1])) vs := by
          rw [hvP] at hv₃
          exact Option.some.inj hv₃
        refine ⟨w, hw, Red.trans ?_ hRw⟩
        refine Red.projRed hfe hnat hilt (by rw [hspa.length, hlenA]) hlenU
          hfctor (by rw [← hlenC]) rfl ?_ hTC0 hTCc hR₃ htele
          hI₁ hD₁ hJ₁ hE₁
        simp only [List.getD, List.getElem?_eq_getElem hidx']
        rfl
      · exact nomatch hvc

end Setlec.SetR
