import Setlec.SetR.Interp2.Step2.CapsRowsP
import Setlec.Verify.Denote.OpenRevDenote
import Setlec.Verify.InstSpine

/-!
# The iota tier's kit (task #161, iota tier)

The two metatheorems the frozen iota law names as owed, plus the
certificate walk that feeds its two telescope premises.

* **`denoteP_openRev`/`denoteP_openRev_base`** — the
  `denote_openRev`/`denote_openRev_base` pair
  (`Verify/Denote/OpenRevDenote.lean`) at the validated reading.
  Mechanical, as the freeze predicted: `denoteP`'s recursion parallels
  `denote`'s and its `fvar` clause ignores the fabricated annotation,
  so the only deltas are the premise swaps the P kit forces —
  `denoteP_lift`/`denoteP_shiftFrom` take `WScoped` where their
  ancestors take `fvarsBelow`, `denoteP_beta` takes the two leaf
  obligations (`hacl`/`hainst`) where `denote_beta` takes `hcl`, and
  the base lemma's lift-invariance is `AVExpr.liftN_eq_self` at the
  erasure's `VExpr.bvarsBelow` (`denoteP_closed`'s route).
* **`teleFitPA_residual`** — `Tele.residual`'s mirror.  `TeleFitPA` is
  *substitution-peeling*, so this is the walk `piResidual` itself
  performs, and the induction is three lines: `denoteP_beta` never
  appears, because the fit already peels at the reading.
* **`certs_telePA`** — `certs_teleR`'s mirror at `TeleFitPA`.  Where
  `certs_teleP` (the caps tier's value-fit sibling) needed the whole
  `teleFitP_of_inst` un-instantiation apparatus, this walk needs
  *none* of it: the frozen fit peels `B.inst a` exactly as `iotaCerts`
  peels `body.instantiate1 arg`, so the two step in lockstep and
  `denoteP_beta` is used only where `certs_teleR` uses `denote_beta`
  — to read the residual.  That is the whole content of the freeze's
  "substitution-peeling restores v1's shape exactly".

The grading tax the caps tier measured is still paid, but at one
remove: `certs_telePA` carries the running type's `AnnotOkP` because
`DefEqClaims2P` demands it of both comparands, and transports it
across the substitution with `AnnotOkP_inst0` — the same two moves.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}
variable {acval : Name → (Name → Nat) → AVExpr}

/-! ## The reverse opening, read -/

/-- **The base-independence of the opened validated reading**
(`denote_openRev_base`'s mirror): a constant-frame subject's reverse
opening reads to the same annotation at every base.  The lift the
induction has to absorb is killed by `AVExpr.liftN_eq_self` at the
erasure's bvar bound — `denoteP_closed`'s route, one depth up. -/
theorem denoteP_openRev_base {cval : TConstVal}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ)
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {e : Expr} (hnf : e.hasFvar = false) {n : Nat}
    (hb : e.looseBVarsBounded n = true) :
    ∀ d : Nat, denoteP acval env φ (d + n) (openRev d n e)
      = denoteP acval env φ n (openRev 0 n e) := by
  intro d
  induction d with
  | zero => rw [Nat.zero_add]
  | succ d ih =>
    have h1 : openRev (d + 1) n e = (openRev d n e).shiftFrom 0 :=
      (openRev_shiftFrom hnf d n).symm
    rw [show d + 1 + n = (d + n) + 1 from by omega, h1,
      denoteP_shiftFrom (p := 0) hacl (openRev d n e) (d + n)
        (Nat.zero_le _)
        (openRev_WScoped (Expr.WScoped.of_not_hasFvar hnf) n),
      ih]
    cases hden : denoteP acval env φ n (openRev 0 n e) with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Option.some.injEq, Nat.sub_zero]
      refine AVExpr.liftN_eq_self v ?_ 1
      have hws : Expr.WScoped n (openRev 0 n e) := by
        have h2 := openRev_WScoped (d := 0)
          (Expr.WScoped.of_not_hasFvar hnf) n
        rwa [Nat.zero_add] at h2
      have hbv := denote_bvarsBelow (cval := cval) (env := env) (φ := φ)
        hcl n (openRev 0 n e) hws
        (openRev_bounded n 0 (by simpa using hb))
        (denoteP_erase hlink n (openRev 0 n e) hden)
      exact hbv.mono (by omega)

/-- **Real-argument instantiation, read through the reverse opening**
(`denote_openRev`'s mirror). -/
theorem denoteP_openRev
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AVExpr) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (as : List Expr) {e : Expr} {d : Nat},
      (∀ a ∈ as, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow d e → e.looseBVarsBounded as.length = true →
      ∀ {vs : List AVExpr}, DenoteSpineP acval env φ d as vs →
      denoteP acval env φ d (Expr.instSeq as (as.length - 1) e)
        = (denoteP acval env φ (d + as.length)
            (openRev d as.length e)).map (AVExpr.instRevChain vs) := by
  intro as
  induction as with
  | nil =>
    intro e d _ _ _ vs hsp
    cases hsp
    show denoteP acval env φ d e = (denoteP acval env φ (d + 0) e).map _
    cases denoteP acval env φ d e <;> rfl
  | cons a as ih =>
    intro e d hargs hfb hb vs hsp
    cases hsp with
    | @cons _ va _ vs' ha hsp' => ?_
    have hargs' : ∀ x ∈ as, Expr.WScoped d x ∧
        x.looseBVarsBounded 0 = true :=
      fun x hx => hargs x (List.mem_cons_of_mem _ hx)
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    show denoteP acval env φ d
      (Expr.instSeq as ((a :: as).length - 1 - 1)
        (e.instantiate1 a ((a :: as).length - 1))) = _
    rw [show (a :: as).length - 1 - 1 = as.length - 1 from by simp,
      show (a :: as).length - 1 = as.length from by simp]
    rw [ih (e := e.instantiate1 a as.length) hargs'
      (Expr.fvarsBelow_instantiate1_gen hwa.fvarsBelow _ hfb)
      (Expr.looseBVarsBounded_instantiate1_gen hba (by simpa using hb))
      hsp']
    -- the opened side: commute the argument out, then β at the top
    rw [openRev_instantiate1_top hba d as.length e]
    have ha' : denoteP acval env φ (d + as.length) a
        = some (va.liftN as.length) := by
      rw [denoteP_lift hacl hwa (d + as.length) (by omega), ha,
        show d + as.length - d = as.length from by omega]
      rfl
    rw [denoteP_beta (n := Name.anonymous) (ty := .sort .zero) hacl hainst
      (openRev_fvarsBelow hfb as.length) (hwa.mono (by omega)) hba ha' 0]
    show ((denoteP acval env φ (d + as.length + 1)
      (openRev d (as.length + 1) e)).map
        (AVExpr.inst · (va.liftN as.length) 0)).map
        (AVExpr.instRevChain vs') = _
    rw [Option.map_map,
      show d + as.length + 1 = d + (a :: as).length from by
        simp only [List.length_cons]
        omega,
      show (a :: as).length = as.length + 1 from rfl]
    cases denoteP acval env φ (d + (as.length + 1))
        (openRev d (as.length + 1) e) with
    | none => rfl
    | some X =>
      simp only [Option.map_some, Option.some.injEq, Function.comp_apply]
      show AVExpr.instRevChain vs' (X.inst (va.liftN as.length) 0) = _
      rw [show AVExpr.instRevChain (va :: vs') X
        = AVExpr.instRevChain vs' (X.inst (va.liftN vs'.length) 0) from rfl,
        hsp'.length]

/-! ## The fit's residual -/

/-- **`Tele.residual`'s mirror**: a `TeleFitPA` fit's residual is the
reading of the checker's own `piResidual`.  `TeleFitPA` peels
`B.inst a` exactly as `piResidual` peels `body.instantiate1 a`, so the
two walks step in lockstep and the only work per step is reading the
peeled body — `denoteP_beta`, once. -/
theorem teleFitPA_residual
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AVExpr) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {ρ : Nat → V} {d : Nat} :
    ∀ (args : List Expr) {ty rest : Expr} {Ta restA : AVExpr}
      {vs : List AVExpr},
      Setlec.piResidual ty args = some rest →
      Expr.WScoped d ty →
      (∀ a ∈ args, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      denoteP acval env φ d ty = some Ta →
      DenoteSpineP acval env φ d args vs →
      TeleFitPA V ρ Ta vs restA →
      denoteP acval env φ d rest = some restA := by
  intro args
  induction args with
  | nil =>
    intro ty rest Ta restA vs hpr _ _ hty hsp hfit
    obtain rfl : rest = ty := (Option.some.inj hpr).symm
    cases hsp
    cases hfit
    exact hty
  | cons a as ih =>
    intro ty rest Ta restA vs hpr hwty hargs hty hsp hfit
    match ty, hpr, hwty, hty with
    | .bvar _, hpr, _, _ => exact nomatch hpr
    | .fvar _ _ _, hpr, _, _ => exact nomatch hpr
    | .sort _, hpr, _, _ => exact nomatch hpr
    | .const _ _, hpr, _, _ => exact nomatch hpr
    | .app _ _, hpr, _, _ => exact nomatch hpr
    | .lam _ _ _ _, hpr, _, _ => exact nomatch hpr
    | .letE _ _ _ _, hpr, _, _ => exact nomatch hpr
    | .lit _, hpr, _, _ => exact nomatch hpr
    | .proj _ _ _, hpr, _, _ => exact nomatch hpr
    | .forallE n dom body mb, hpr, hwty, hty => ?_
    cases hsp with | @cons _ va _ vs' ha hsp' => ?_
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteP_forallE_inv hty
    have hbody' : denoteP acval env φ d (body.instantiate1 a)
        = some (bodya.inst va) := by
      rw [denoteP_beta hacl hainst (n := n) (ty := dom)
        hbodyw.fvarsBelow hwa hba ha 0, hbodya]
      rfl
    cases hfit with
    | cons _ hfit' =>
      exact ih hpr (Expr.WScoped.instantiate1_gen hwa 0 hbodyw)
        (fun x hx => hargs x (List.mem_cons_of_mem a hx)) hbody' hsp' hfit'

/-! ## `certs_telePA` — a certified spine fits the reading

`certs_teleR`'s mirror.  Two deltas from `certs_teleP`, both in the
P lane's favour:

* the **un-instantiation apparatus is gone**.  `certs_teleP` had to
  recover `bodya` under `cons` from `bodya.inst aa`, which is false
  without the `PiChainP` guard; `TeleFitPA` peels to `bodya.inst aa`
  itself, so there is nothing to recover and no guard to supply.
* the **residual is hoisted out of the `∀ ρ`**.  It is an `AVExpr`
  fixed by the walk, not a `V` fixed by the valuation, so one residual
  serves every environment — which is what lets the consumer feed the
  *same* `restC` to the fit and to `IotaIndexPinP`.

The spine's readings stay an input and the running type's grading is
still carried, exactly as in `certs_teleP`. -/

/-- **A certified spine fits the type's reading, substitution-peeling.**
One step is `InferReadsP` (the argument's type reads),
`InferClaims2P` (it is graded and the argument inhabits it) and
`DefEqClaims2P` (it is the domain) — the checker's own order. -/
theorem certs_telePA {m : EnvS2Core V env}
    (ihd : DefEqClaims2P μ m φ fuel) (ihi : InferClaims2P μ m φ fuel)
    (hreads : InferReadsP m μ φ fuel) :
    ∀ {d : Nat} {Δa : List AVExpr} (ty : Expr) (args : List Expr)
      (vs : List AVExpr) (Ta : AVExpr),
      Setlec.iotaCertsP μ env fuel d ty args = .ok true →
      Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
      Expr.LeavesBounded ty → CtxOkP m φ d Δa ty →
      denoteP m.acval env φ d ty = some Ta →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ Ta) →
      (∀ x ∈ args, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x) →
      DenoteSpineP m.acval env φ d args vs →
      ∃ resta : AVExpr,
        (∀ ρ : Nat → V, Sat2 V Δa ρ → TeleFitPA V ρ Ta vs resta) ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ resta) ∧
        (∀ x ∈ vs, ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ x) := by
  intro d Δa ty args
  induction args generalizing ty with
  | nil =>
    intro vs Ta _ _ _ _ _ _ hokT _ hsp
    cases hsp
    exact ⟨Ta, fun _ _ => .nil, hokT, by simp⟩
  | cons a as ih =>
    intro vs Ta hc hwty hbty hLbty hCty hity hokT hargs hsp
    match ty, hc, hwty, hbty, hLbty, hCty, hity with
    | .bvar _, hc, _, _, _, _, _ => exact nomatch hc
    | .fvar _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .sort _, hc, _, _, _, _, _ => exact nomatch hc
    | .const _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .app _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .lam _ _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .letE _ _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .lit _, hc, _, _, _, _, _ => exact nomatch hc
    | .proj _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .forallE n dom body mb, hc, hwty, hbty, hLbty, hCty, hity => ?_
    obtain ⟨ta, hta, hde, hrestc⟩ := Setlec.iotaCerts_step_inv hc
    obtain ⟨haw, hab, haLb, haC⟩ := hargs a List.mem_cons_self
    cases hsp with | @cons _ aa _ vs' haa hsp' => ?_
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨hdomb, hbodyb⟩ :
        dom.looseBVarsBounded 0 = true ∧
          Expr.looseBVarsBounded 1 body = true := by
      simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
    have hLbdom : Expr.LeavesBounded dom := fun l hl =>
      hLbty l (by simp [Expr.fvarLeaves, hl])
    have hCdom : CtxOkP m φ d Δa dom :=
      hCty.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteP_forallE_inv hity
    -- the reading's grading, hoisted through the `.pi` clause
    have hokDom : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ doma :=
      fun ρ hρ =>
        ⟨((AnnotOk2_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).1).1,
          ((AnnotValidV_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).2).1⟩
    have hokBody : ∀ (ρ : Nat → V), Sat2 V Δa ρ →
        ∀ x, x ∈ˢ interp2 V ρ doma → AnnotOkP V (cons x ρ) bodya :=
      fun ρ hρ x hx =>
        ⟨((AnnotOk2_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).1).2 x hx,
          ((AnnotValidV_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).2).2.1 x hx⟩
    -- the argument's inferred type reads, is graded, and holds it
    obtain ⟨taa, htaa⟩ :=
      hreads hta haw hab haLb (LeafReadsP.of_ctxOkP haC) haa
    obtain ⟨hokA, hokTa, hmemA⟩ := ihi hta haw hab haLb haC haa htaa
    have hwta : Expr.WScoped d ta :=
      Setlec.inferTypeCore_WScoped m.base.wf fuel hta haw
    have hbta : ta.looseBVarsBounded 0 = true :=
      Setlec.inferTypeCore_looseBVars m.base.wf fuel hta haw hab haLb
    have hLta : Expr.LeavesBounded ta := fun l hl =>
      haLb l (Setlec.inferTypeCore_fvarLeaves m.base.wf fuel hta haw l hl)
    have hCta : CtxOkP m φ d Δa ta :=
      haC.of_subset (Setlec.inferTypeCore_fvarLeaves m.base.wf fuel hta haw)
    have hdeq : ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ taa = interp2 V ρ doma :=
      ihd hde hwta hbta hLta hdomw hdomb hLbdom hCta hCdom htaa hdoma
        hokTa hokDom
    -- the residual reads, by β on the reading
    have hbody' : denoteP m.acval env φ d (body.instantiate1 a)
        = some (bodya.inst aa) := by
      rw [denoteP_beta m.acval_closed (acval_inst_self m)
        (n := n) (ty := dom) hbodyw.fvarsBelow haw hab haa 0, hbodya]
      rfl
    have hwbody : Expr.WScoped d (body.instantiate1 a) :=
      Expr.WScoped.instantiate1_gen haw 0 hbodyw
    have hbbody : (body.instantiate1 a).looseBVarsBounded 0 = true :=
      Expr.looseBVarsBounded_instantiate1_gen hab hbodyb
    have hLbbody : Expr.LeavesBounded (body.instantiate1 a) := by
      intro l hl
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
      · exact hLbty l (by simp [Expr.fvarLeaves, hl'])
      · exact haLb l hl'
    have hCbody : CtxOkP m φ d Δa (body.instantiate1 a) := by
      refine ⟨hCty.1, fun l hl => ?_⟩
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
      · exact hCty.2 l (by simp [Expr.fvarLeaves, hl'])
      · exact haC.2 l hl'
    have hokBody' : ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOkP V ρ (bodya.inst aa) := fun ρ hρ =>
      (AnnotOkP_inst0 (hokA ρ hρ)).mpr
        (hokBody ρ hρ _ ((hdeq ρ hρ) ▸ hmemA ρ hρ))
    -- the tail, and the fit
    obtain ⟨resta, hfit, hokR, hokAs⟩ :=
      ih (body.instantiate1 a) _ _ hrestc hwbody hbbody hLbbody hCbody
        hbody' hokBody' (fun x hx => hargs x (List.mem_cons_of_mem a hx))
        hsp'
    refine ⟨resta, fun ρ hρ =>
      .cons ((hdeq ρ hρ) ▸ hmemA ρ hρ) (hfit ρ hρ), hokR, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hokA
    · exact hokAs x hx'

/-! ## From a substitution-peeling fit to a graded application

`annotOkP_mkAppN_of_fit`'s twin at `TeleFitPA`.  The caps version keeps
the type's environment `σ` separate from the spine's `ρ` because its
fit peels into `cons`-extensions; this one peels by substitution, so
there is one environment throughout and `interp2_inst0` is the only
commutation. -/

/-- **A `TeleFitPA` fit plus the type's grading grades the applied
spine**, and places it in the residual's reading. -/
theorem annotOkP_mkAppN_of_fitA {ρ : Nat → V} :
    ∀ (vs : List AVExpr) {Ta f rest : AVExpr},
      AnnotOkP V ρ Ta → AnnotOkP V ρ f →
      (∀ x ∈ vs, AnnotOkP V ρ x) →
      interp2 V ρ f ∈ˢ interp2 V ρ Ta →
      TeleFitPA V ρ Ta vs rest →
      AnnotOkP V ρ (AVExpr.mkAppN f vs) ∧
        interp2 V ρ (AVExpr.mkAppN f vs) ∈ˢ interp2 V ρ rest := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f rest _ hf _ hmem hfit
    cases hfit
    exact ⟨hf, hmem⟩
  | cons x xs ih =>
    intro Ta f rest hokT hf hoks hmem hfit
    cases hfit with
    | @cons u v A B _ _ _ hx hfit' =>
      have hokA : AnnotOkP V ρ A :=
        ⟨((AnnotOk2_pi V ρ u v A B) ▸ hokT.1).1,
          ((AnnotValidV_pi V ρ u v A B) ▸ hokT.2).1⟩
      have hokB : ∀ y, y ∈ˢ interp2 V ρ A → AnnotOkP V (cons y ρ) B :=
        fun y hy =>
          ⟨((AnnotOk2_pi V ρ u v A B) ▸ hokT.1).2 y hy,
            ((AnnotValidV_pi V ρ u v A B) ▸ hokT.2).2.1 y hy⟩
      have hfib : v = 0 → ∀ y, y ∈ˢ interp2 V ρ A →
          interp2 V (cons y ρ) B ∈ˢ (univZero : V) :=
        ((AnnotValidV_pi V ρ u v A B) ▸ hokT.2).2.2
      rw [interp2_pi] at hmem
      have hokx : AnnotOkP V ρ x := hoks x List.mem_cons_self
      have hstep : AnnotOkP V ρ (.app f x) := by
        refine ⟨?_, ?_⟩
        · rw [AnnotOk2_app]
          exact ⟨hf.1, hokx.1, v, interp2 V ρ A,
            (fun y => interp2 V (cons y ρ) B), hmem, hx, hfib⟩
        · rw [AnnotValidV_app]; exact ⟨hf.2, hokx.2⟩
      have hmem' : interp2 V ρ (.app f x) ∈ˢ interp2 V ρ (B.inst x) := by
        rw [interp2_inst0, interp2_app]
        exact app_mem_piR hmem hx hfib
      exact ih ((AnnotOkP_inst0 hokx).mpr (hokB _ hx)) hstep
        (fun y hy => hoks y (List.mem_cons_of_mem x hy)) hmem' hfit'


/-! ## The `instRevChain` grading closure (the iota seal's ratified
repair, consumption side)

The strengthened `RecRuleLawP` carries the open pins' readings graded
at **every** environment; the row grades the *instantiated* comparand
by unfolding the chain through the `AnnotOk2_inst`/`AnnotValidV_inst`
iffs.  The unfolding flows outside-in, so the closure is proved as an
**iff at a generalized body** (the structural induction with a
one-directional statement traps itself: the tail's hypothesis would
need the head argument graded at every environment, which an
open-context argument reading never is). -/

/-- The cons-chain environment the unfolding lands in.  Its shape is
irrelevant to consumers — the substituted body is `∀ σ`-graded — but
the arguments' gradings are needed at the *ambient* environment only,
because each `liftN` pops the chain back down (`shiftE_envChainP`). -/
noncomputable def envChainP (ρ : Nat → V) : List AVExpr → Nat → V
  | [] => ρ
  | v :: vs => cons (interp2 V ρ v) (envChainP ρ vs)

theorem shiftE_envChainP (ρ : Nat → V) :
    ∀ vs : List AVExpr, shiftE vs.length 0 (envChainP ρ vs) = ρ := by
  intro vs
  induction vs with
  | nil => funext i; simp [shiftE, envChainP]
  | cons v vs ih =>
    funext i
    have h := congrFun ih (i)
    simp only [envChainP, List.length_cons, shiftE] at h ⊢
    simp only [Nat.not_lt_zero, if_false] at h ⊢
    show (cons (interp2 V ρ v) (envChainP ρ vs)) (i + (vs.length + 1))
      = ρ i
    rw [show i + (vs.length + 1) = (i + vs.length) + 1 from by omega,
      cons_succ]
    simpa [shiftE] using h

/-- Truthfulness through the reverse substitution chain, as an iff at
a generalized body. -/
theorem AnnotOk2_instRevChain (ρ : Nat → V) :
    ∀ (vs : List AVExpr), (∀ v ∈ vs, AnnotOk2 V ρ v) →
      ∀ X : AVExpr,
        (AnnotOk2 V ρ (Setlec.SetR.AVExpr.instRevChain vs X) ↔
          AnnotOk2 V (envChainP ρ vs) X) := by
  intro vs
  induction vs with
  | nil => intro _ X; exact Iff.rfl
  | cons v vs ih =>
    intro hvs X
    show AnnotOk2 V ρ (Setlec.SetR.AVExpr.instRevChain vs
        (X.inst (v.liftN vs.length) 0)) ↔ _
    rw [ih (fun v' hv' => hvs v' (List.mem_cons_of_mem _ hv'))]
    have hva : AnnotOk2 V (shiftE 0 0 (envChainP ρ vs))
        (v.liftN vs.length) := by
      rw [shiftE_zero_zero, AnnotOk2_liftN, shiftE_envChainP]
      exact hvs v List.mem_cons_self
    rw [AnnotOk2_inst V X (v.liftN vs.length) 0 (envChainP ρ vs) hva]
    rw [show instE 0 (interp2 V (shiftE 0 0 (envChainP ρ vs))
          (v.liftN vs.length)) (envChainP ρ vs)
        = envChainP ρ (v :: vs) from by
      rw [shiftE_zero_zero, instE_zero, interp2_liftN,
        shiftE_envChainP]
      rfl]

/-- Bit validity through the chain — the identical unfolding. -/
theorem AnnotValidV_instRevChain (ρ : Nat → V) :
    ∀ (vs : List AVExpr), (∀ v ∈ vs, AnnotValidV V ρ v) →
      ∀ X : AVExpr,
        (AnnotValidV V ρ (Setlec.SetR.AVExpr.instRevChain vs X) ↔
          AnnotValidV V (envChainP ρ vs) X) := by
  intro vs
  induction vs with
  | nil => intro _ X; exact Iff.rfl
  | cons v vs ih =>
    intro hvs X
    show AnnotValidV V ρ (Setlec.SetR.AVExpr.instRevChain vs
        (X.inst (v.liftN vs.length) 0)) ↔ _
    rw [ih (fun v' hv' => hvs v' (List.mem_cons_of_mem _ hv'))]
    have hva : AnnotValidV V (shiftE 0 0 (envChainP ρ vs))
        (v.liftN vs.length) := by
      rw [shiftE_zero_zero, AnnotValidV_liftN, shiftE_envChainP]
      exact hvs v List.mem_cons_self
    rw [AnnotValidV_inst V X (v.liftN vs.length) 0 (envChainP ρ vs)
      hva]
    rw [show instE 0 (interp2 V (shiftE 0 0 (envChainP ρ vs))
          (v.liftN vs.length)) (envChainP ρ vs)
        = envChainP ρ (v :: vs) from by
      rw [shiftE_zero_zero, instE_zero, interp2_liftN,
        shiftE_envChainP]
      rfl]

/-- **The closure**: an `∀ σ`-graded body substituted along
ambient-graded arguments is graded at the ambient environment. -/
theorem annotOkP_instRevChain {ρ : Nat → V} {vs : List AVExpr}
    {X : AVExpr} (hX : ∀ σ : Nat → V, AnnotOkP V σ X)
    (hvs : ∀ v ∈ vs, AnnotOkP V ρ v) :
    AnnotOkP V ρ (Setlec.SetR.AVExpr.instRevChain vs X) :=
  ⟨(AnnotOk2_instRevChain ρ vs (fun v hv => (hvs v hv).1) X).mpr
      (hX _).1,
    (AnnotValidV_instRevChain ρ vs (fun v hv => (hvs v hv).2) X).mpr
      (hX _).2⟩

end Setlec.SetR.Interp2
