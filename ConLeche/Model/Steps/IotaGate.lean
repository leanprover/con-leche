module

public import ConLeche.Model.Steps.IotaKit
import ConLeche.Model.IOLicense
public section

/-!
# The ι-slot licence (the ι batch, 2026-09-05)

`iotaCerts` at a *licensed* walk (`lic = true`, set by `iotaRec`'s two
telescope runs only) skips a slot whose `∀`-binder datum is `.never`.
This module supplies what the skipped run used to: the slot's
membership `⟦a⟧ ∈ ⟦A⟧` for `TeleFitPA.cons`.

* `iota_slot_transfer` — ONE SLOT: the licence is `io_domain_transfer`
  with its arguments renamed.  The premise is the regime of the product
  the head-prefix inhabits (`piR v A B`, `v ≠ 0`), and the regime of a
  product IS its codomain sort's bit (`piR`'s numeral; `denoteMeta`'s
  `.forallE` clause reads `pwBit φ m.pw` of exactly the node the walk
  peels).  The domain `A` is unconstrained — its own kind is irrelevant.
* `certs_teleLic` — the walk (`certs_telePA`'s licensed twin): the
  redex's own `WellDenotedV` carries every prefix's app slot
  (`WellDenoted_app`), and the head's membership in the telescope's
  reading (`mem_type`, via `constType_pkg`) is carried down the
  telescope by `wellDenotedV_mkAppN_of_fitA` one slot at a time.  At a
  licensed slot the membership is the transfer; at a certified slot it
  is the run's.  The ungated `TeleFitPA` comes out, so the law's
  premise is unchanged.
* `iota_slot_fence` — the fence: at a squash-regime product every
  premise of the licence holds and the slot membership is false
  (`io_squash_no_transfer`'s witness, roles renamed).  With
  `isNever_iff_forall_pwBit_ne_zero`'s completeness half, the licensed
  fragment is exactly `.never`, as for β and io.

The rescue's synthetic-spine certifications stay at `lic = false`
(`certs_telePA`): a fabricated `ctor p⃗ (proj_i major)` is not a subterm
of the subject, carries no slot, and its grading is *produced* by that
run — gating it would be circular (DESIGN.md, "THE ι AUDIT" §9.1.4).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level BinderMeta PropWhen)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## One slot -/

/-- **THE ι-SLOT LICENCE, one slot.**  `f` is the head-prefix
`rec p⃗ … a_{i-1}` (or the constructor prefix), `piR v A B` the reading
of the telescope's next binder — `v` its codomain-sort bit — and the
slot `f ∈ piR v' A' B' ∧ a ∈ A'` is the redex's own `WellDenoted` app
package at that prefix.  At `v ≠ 0` the graph pins the domain and the
argument lands in the telescope's domain: `TeleFitPA.cons`'s premise,
with no run.  This is `io_domain_transfer` verbatim. -/
theorem iota_slot_transfer {v v' : Nat} {A A' f a : V} {B B' : V → V}
    (hv : v ≠ 0) (hf : f ∈ˢ piR v A B)
    (hslot : f ∈ˢ piR v' A' B') (ha : a ∈ˢ A') : a ∈ˢ A :=
  io_domain_transfer hv hslot ha hf

/-! ## Spine gradings -/

/-- The head of a graded spine is graded (`hoist_spine`'s first
conjunct at one valuation). -/
theorem wellDenotedV_mkAppN_head {ρ : Nat → V} :
    ∀ (as : List AnnotTerm) {f : AnnotTerm},
      WellDenotedV V ρ (AnnotTerm.mkAppN f as) → WellDenotedV V ρ f
  | [], _, h => h
  | a :: as, f, h => by
    have h' : WellDenotedV V ρ (.app f a) := wellDenotedV_mkAppN_head as h
    exact ⟨((WellDenoted_app V ρ f a) ▸ h'.1).1,
      ((AnnotValid_app V ρ f a) ▸ h'.2).1⟩

theorem AnnotTerm.mkAppN_append (f : AnnotTerm) :
    ∀ (as bs : List AnnotTerm),
      AnnotTerm.mkAppN f (as ++ bs) = AnnotTerm.mkAppN (AnnotTerm.mkAppN f as) bs
  | [], _ => rfl
  | _ :: as, bs => AnnotTerm.mkAppN_append _ as bs

/-- **An app's argument may be exchanged for an interpretation-equal
graded one**: the slot is about `⟦a⟧`, so it transfers. -/
theorem wellDenotedV_app_congr_arg {ρ : Nat → V} {f a a' : AnnotTerm}
    (h : WellDenotedV V ρ (.app f a)) (ha' : WellDenotedV V ρ a')
    (heq : interp V ρ a = interp V ρ a') :
    WellDenotedV V ρ (.app f a') := by
  obtain ⟨h1, h2⟩ := h
  rw [WellDenoted_app] at h1
  rw [AnnotValid_app] at h2
  obtain ⟨hf, -, v, A, B, hslot, hmem, hcod⟩ := h1
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_app]
    exact ⟨hf, ha'.1, v, A, B, hslot, heq ▸ hmem, hcod⟩
  · rw [AnnotValid_app]
    exact ⟨h2.1, ha'.2⟩

/-- The same at a spine's last argument (the recursor spine's major
slot: the walk is handed the rescued major, the subject carries the
original — `heqAll` identifies their interpretations). -/
theorem wellDenotedV_mkAppN_snoc_congr {ρ : Nat → V} {f a a' : AnnotTerm}
    {as : List AnnotTerm}
    (h : WellDenotedV V ρ (AnnotTerm.mkAppN f (as ++ [a]))) (ha' : WellDenotedV V ρ a')
    (heq : interp V ρ a = interp V ρ a') :
    WellDenotedV V ρ (AnnotTerm.mkAppN f (as ++ [a'])) := by
  rw [AnnotTerm.mkAppN_append] at h ⊢
  exact wellDenotedV_app_congr_arg h ha' heq

/-! ## The licensed walk -/

/-- **A licensed-and-certified spine fits the type's reading**
(`certs_telePA`'s twin at `lic`).  Two inputs beyond `certs_telePA`'s:
the redex's own grading `WellDenotedV (mkAppN fa vs)` — the supplier of
every prefix's app slot — and the head's membership in the telescope's
reading.  At a licensed slot the membership is `iota_slot_transfer`
on the slot; at a certified slot it is the run's (`certs_telePA`'s
step verbatim).  No certificate appears at a licensed slot. -/
theorem certs_teleLic {m : EnvModel V env}
    (ihd : DefEqClaim μ m φ fuel) (ihis : InferClaimIOS μ m φ fuel)
    (hexi : InferExistsIOS μ m φ fuel) {lic : Bool} :
    ∀ {d : Nat} {Δa : List AnnotTerm} (ty : Expr) (args : List Expr)
      (vs : List AnnotTerm) (Ta fa : AnnotTerm),
      ConLeche.iotaCertsFueled μ env fuel d lic ty args = .ok true →
      Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
      Expr.LeavesBounded ty → CtxOk m φ d Δa ty →
      denoteMeta m.acval env φ d ty = some Ta →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Ta) →
      (∀ x ∈ args, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOk m φ d Δa x) →
      DenoteMetaSpine m.acval env φ d args vs →
      (∀ x ∈ vs, ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ x) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (AnnotTerm.mkAppN fa vs)) →
      (∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ fa ∈ˢ interp V ρ Ta) →
      ∃ resta : AnnotTerm,
        (∀ ρ : Nat → V, Sat V Δa ρ → TeleFitPA V ρ Ta vs resta) ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ resta) ∧
        (∀ x ∈ vs, ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ x) := by
  intro d Δa ty args
  induction args generalizing ty with
  | nil =>
    intro vs Ta fa _ _ _ _ _ _ hokT _ hsp _ _ _
    cases hsp
    exact ⟨Ta, fun _ _ => .nil, hokT, by simp⟩
  | cons a as ih =>
    intro vs Ta fa hc hwty hbty hLbty hCty hity hokT hargs hsp hokvs hokS hfa
    match ty, hc, hwty, hbty, hLbty, hCty, hity with
    | .bvar _, hc, _, _, _, _, _ => exact nomatch hc
    | .fvar _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .sort _, hc, _, _, _, _, _ => exact nomatch hc
    | .const _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .app _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .lam _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .letE _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .lit _, hc, _, _, _, _, _ => exact nomatch hc
    | .proj _ _ _, hc, _, _, _, _, _ => exact nomatch hc
    | .forallE dom body mb, hc, hwty, hbty, hLbty, hCty, hity => ?_
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
    have hCdom : CtxOk m φ d Δa dom :=
      hCty.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hity
    -- the reading's grading, hoisted through the `.pi` clause
    have hokDom : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ doma :=
      fun ρ hρ =>
        ⟨((WellDenoted_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).1).1,
          ((AnnotValid_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).2).1⟩
    have hokBody : ∀ (ρ : Nat → V), Sat V Δa ρ →
        ∀ x, x ∈ˢ interp V ρ doma → WellDenotedV V (cons x ρ) bodya :=
      fun ρ hρ x hx =>
        ⟨((WellDenoted_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).1).2 x hx,
          ((AnnotValid_pi V ρ 0 _ doma bodya) ▸ (hokT ρ hρ).2).2.1 x hx⟩
    have hokA : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa :=
      hokvs aa List.mem_cons_self
    -- the redex's app slot at this prefix, and the head-prefix's grading
    have hokApp : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (.app fa aa) :=
      fun ρ hρ => wellDenotedV_mkAppN_head vs' (hokS ρ hρ)
    have hokFa : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ fa :=
      fun ρ hρ =>
        ⟨((WellDenoted_app V ρ fa aa) ▸ (hokApp ρ hρ).1).1,
          ((AnnotValid_app V ρ fa aa) ▸ (hokApp ρ hρ).2).1⟩
    -- **THE SLOT MEMBERSHIP**: licensed or certified
    obtain ⟨hmemA, hrestc⟩ : (∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ aa ∈ˢ interp V ρ doma) ∧
        ConLeche.iotaCertsFueled μ env fuel d lic (body.instantiate1 a) as
          = .ok true := by
      rcases ConLeche.iotaCerts_step_inv_gate hc with ⟨hg, hrestc⟩ |
          ⟨ta, hta, hde, hrestc⟩
      · -- THE LICENSED ARM: the binder's datum is `.never`, the head
        -- prefix inhabits the binder's product reading, the slot
        -- transfers
        refine ⟨fun ρ hρ => ?_, hrestc⟩
        have hv : pwBit φ mb.pw ≠ 0 :=
          pwBit_ne_zero_of_isNever (Bool.and_eq_true .. |>.mp hg).2 φ
        obtain ⟨v', A', B', hslot, ha, -⟩ :=
          ((WellDenoted_app V ρ fa aa) ▸ (hokApp ρ hρ).1).2.2
        have hf' := hfa ρ hρ
        rw [interp_pi] at hf'
        exact iota_slot_transfer hv hf' hslot ha
      · -- THE CERTIFIED ARM: `certs_telePA`'s step
        refine ⟨?_, hrestc⟩
        obtain ⟨taa, htaa⟩ := hexi hta haw hab haLb haC haa
        obtain ⟨hokTa, hmemA⟩ := ihis hta haw hab haLb haC haa htaa hokA
        have hwta : Expr.WScoped d ta :=
          ConLeche.inferTypeIO_WScoped m.wf fuel hta haw
        have hbta : ta.looseBVarsBounded 0 = true :=
          ConLeche.inferTypeIO_looseBVars m.wf fuel hta haw hab haLb
        have hLta : Expr.LeavesBounded ta := fun l hl =>
          haLb l (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hta haw l hl)
        have hCta : CtxOk m φ d Δa ta :=
          haC.of_subset (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hta haw)
        have hdeq : ∀ ρ : Nat → V, Sat V Δa ρ →
            interp V ρ taa = interp V ρ doma :=
          ihd hde hwta hbta hLta hdomw hdomb hLbdom hCta hCdom htaa hdoma
            hokTa hokDom
        exact fun ρ hρ => (hdeq ρ hρ) ▸ hmemA ρ hρ
    -- the residual reads, by β on the reading
    have hbody' : denoteMeta m.acval env φ d (body.instantiate1 a)
        = some (bodya.inst aa) := by
      rw [denoteMeta_beta m.acval_closed (acval_inst_self m)
        (ty := dom) hbodyw.fvarsBelow haw hab haa 0, hbodya]
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
    have hCbody : CtxOk m φ d Δa (body.instantiate1 a) := by
      refine ⟨hCty.1, fun l hl => ?_⟩
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
      · exact hCty.2 l (by simp [Expr.fvarLeaves, hl'])
      · exact haC.2 l hl'
    have hokBody' : ∀ ρ : Nat → V, Sat V Δa ρ →
        WellDenotedV V ρ (bodya.inst aa) := fun ρ hρ =>
      (WellDenotedV_inst0 (hokA ρ hρ)).mpr (hokBody ρ hρ _ (hmemA ρ hρ))
    -- the applied prefix inhabits the peeled reading
    have hfa' : ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ (.app fa aa) ∈ˢ interp V ρ (bodya.inst aa) := by
      intro ρ hρ
      have hoks : ∀ x ∈ [aa], WellDenotedV V ρ x := by
        intro x hx
        rw [List.mem_singleton] at hx
        subst hx
        exact hokA ρ hρ
      exact (wellDenotedV_mkAppN_of_fitA [aa] (hokT ρ hρ) (hokFa ρ hρ) hoks
        (hfa ρ hρ) (TeleFitPA.cons (hmemA ρ hρ) .nil)).2
    -- the tail, and the fit
    obtain ⟨resta, hfit, hokR, hokAs⟩ :=
      ih (body.instantiate1 a) _ _ (.app fa aa) hrestc hwbody hbbody hLbbody
        hCbody hbody' hokBody' (fun x hx => hargs x (List.mem_cons_of_mem a hx))
        hsp' (fun x hx => hokvs x (List.mem_cons_of_mem aa hx)) hokS hfa'
    refine ⟨resta, fun ρ hρ => .cons (hmemA ρ hρ) (hfit ρ hρ), hokR,
      fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hokA
    · exact hokAs x hx'

/-! ## The fence -/

/-- **THE ι-SLOT FENCE.**  At a squash-regime binder (`v = 0`: the
datum is not `.never`, and holds at some valuation) every premise of
`iota_slot_transfer` is satisfiable with the argument OUTSIDE the
telescope's domain: the head-prefix inhabits the telescope's product
(vacuously — `pt ∈ piR 0 ∅ B`), the redex's slot holds (`pt ∈ piR 0
(truthVal True) B'`, `pt ∈ truthVal True`), and `pt ∉ ∅`.  The
membership `TeleFitPA.cons` needs is false, so the skip is unlicensed
there — the same witness as `io_squash_no_transfer`, roles renamed. -/
theorem iota_slot_fence :
    ∃ (A A' f a : V) (B B' : V → V),
      f ∈ˢ piR 0 A B ∧                 -- the telescope's product, squash regime
      f ∈ˢ piR 0 A' B' ∧ a ∈ˢ A' ∧     -- the redex's own slot
      ¬ a ∈ˢ A := by
  obtain ⟨A, A', f, a, B, B', h1, h2, -, h4, h5⟩ :=
    io_squash_no_transfer (V := V)
  exact ⟨A', A, f, a, B', B, h4, h1, h2, h5⟩

/-- The licence is exactly `.never`: the fence's `v = 0` is reachable
from every other datum at the all-zero valuation
(`isNever_iff_forall_pwBit_ne_zero`'s completeness half), so no datum
but `.never` puts every valuation on the licensed side. -/
theorem iota_gate_exact {pw : PropWhen} :
    PropWhen.isNever pw = true ↔ ∀ φ : Name → Nat, pwBit φ pw ≠ 0 :=
  isNever_iff_forall_pwBit_ne_zero

end ConLeche.Model
