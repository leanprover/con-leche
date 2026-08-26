import Setlec.TTVerify.Tele
import Setlec.TTVerify.Claims
import Setlec.Verify.InferLeaves

/-!
# Telescope certification, transposed

`certs_typed` — the transpose of `certs_fit`
(`Setlec/Model/Core/Certs.lean`): a successful `iotaCerts` run builds a
`TeleTyped` for the certified spine.

**This is the `iotaCerts` prediction of `Setlec/TTVerify/DESIGN.md` §6
discharged on the positive side.**  The prediction was that the checker
already computes exactly the per-argument facts the fired iota contract
needs; the proof below is that claim, mechanized.  Each step consumes
precisely what `iotaCerts` produces — `infer arg` then
`defeq ta dom` — and yields `HasType Δ ⟦arg⟧ ⟦dom⟧`, one premise per
argument, at the domain the rule will fire at.

Everything the proof needs beyond the claims lives in
`Setlec/Verify/*` (`iotaCerts_step_inv`, `inferTypeCore_fvarLeaves`
and friends), so the transposition needed no re-derivation of the
inversion — one of the two things checking the prediction early bought.

Two differences from the original, both of them savings:

* the model threads `vs` and an `InterpSpine` hypothesis to fix the
  argument values; here the inference claim *produces* the denotations,
  so the spine is existential;
* every `AnnotOk` premise disappears, so the per-argument side
  conditions are the three syntactic ones and nothing else.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- `CtxOk` only reads the leaf set, so it restricts along any subset
of leaves.  (The `Δ.length` conjunct is carried, not re-derived.) -/
theorem CtxOk.of_subset {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {e e' : Expr}
    (hsub : ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves)
    (h : CtxOk cval env φ d Δ e) : CtxOk cval env φ d Δ e' :=
  ⟨h.1, fun l hl => h.2 l (hsub l hl)⟩

/-- **A certified spine is a typed telescope.**  Transpose of
`certs_fit`. -/
theorem certs_typed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel) :
    ∀ {d : Nat} {Δ : List VExpr} (ty : Expr) (args : List Expr) (T : VExpr),
      iotaCertsP env fuel d ty args = .ok true →
      Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
      CtxOk m.cval env φ d Δ ty →
      denote m.cval env φ d ty = some T →
      (∀ x ∈ args, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        CtxOk m.cval env φ d Δ x) →
      ∃ xs rest, TeleTyped m.cval env φ d Δ ty args xs rest := by
  intro d Δ ty args
  induction args generalizing ty with
  | nil => intro T _ _ _ _ _ _; exact ⟨[], ty, TeleTyped.nil⟩
  | cons a as ih =>
    intro T hc hwty hbty hCty hity hargs
    match ty, hc with
    | .bvar _, hc => exact nomatch hc
    | .fvar _ _ _, hc => exact nomatch hc
    | .sort _, hc => exact nomatch hc
    | .const _ _, hc => exact nomatch hc
    | .app _ _, hc => exact nomatch hc
    | .lam _ _ _ _, hc => exact nomatch hc
    | .letE _ _ _ _, hc => exact nomatch hc
    | .lit _, hc => exact nomatch hc
    | .proj _ _ _, hc => exact nomatch hc
    | .forallE n dom body mt, hc =>
    obtain ⟨ta, hta, hde, hrest⟩ := iotaCerts_step_inv hc
    obtain ⟨haw, hab, haC⟩ := hargs a List.mem_cons_self
    -- the telescope's own scoping, split
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨hdomb, hbodyb⟩ :
        dom.looseBVarsBounded 0 = true ∧
          Expr.looseBVarsBounded 1 body = true := by
      simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
    have hCdom : CtxOk m.cval env φ d Δ dom :=
      CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCty
    -- the domain and the opened body denote (the ∀ clause forces it)
    rw [denote_forallE] at hity
    split at hity
    · exact nomatch hity
    · next A hidom =>
      split at hity
      · exact nomatch hity
      · next B hibody =>
        -- the argument's inferred type denotes, and is `Deq` to the domain
        obtain ⟨x, tv, hix, hita, hxt⟩ := ihi hta haC
        have hCta : CtxOk m.cval env φ d Δ ta :=
          CtxOk.of_subset
            (inferTypeCore_fvarLeaves m.wf fuel hta haw) haC
        have hDeq : Deq Δ tv A := ihd hde hCta hCdom hita hidom
        -- …so the argument is typed at the domain: one premise, at the
        -- domain the rule fires at
        have hxA : HasType Δ x A := Deq.conv hxt hDeq
        -- the instantiated residual denotes, by `denote_beta`
        have hfb : Expr.fvarsBelow d body := hbodyw.fvarsBelow
        have hibody' :
            denote m.cval env φ d (body.instantiate1 a) =
              some (VExpr.inst B x) := by
          rw [denote_beta (n := n) (ty := dom) hcl hfb haw hab hix 0, hibody]
          rfl
        have hwbody : Expr.WScoped d (body.instantiate1 a) :=
          Expr.WScoped.instantiate1_gen haw 0 hbodyw
        have hbbody : (body.instantiate1 a).looseBVarsBounded 0 = true :=
          Expr.looseBVarsBounded_instantiate1_gen hab hbodyb
        have hCbody : CtxOk m.cval env φ d Δ (body.instantiate1 a) := by
          refine ⟨hCty.1, fun l hl => ?_⟩
          rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
          · exact hCty.2 l (by simp [Expr.fvarLeaves, hl'])
          · exact haC.2 l hl'
        obtain ⟨xs, rest, hfit⟩ :=
          ih (body.instantiate1 a) (VExpr.inst B x) hrest hwbody hbbody
            hCbody hibody' (fun y hy => hargs y (List.mem_cons_of_mem a hy))
        exact ⟨x :: xs, rest,
          TeleTyped.cons hidom hix hxA hfb haw hab hfit⟩

end Setlec.TTVerify
