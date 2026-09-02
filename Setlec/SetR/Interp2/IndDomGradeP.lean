import Setlec.SetR.Interp2.IndGradeP

/-!
# The instantiated domains are graded (task #161, IND TIER part 4)

The second half of the part-4 grading bill, and the one that is
**genuinely new content** rather than a transposition.

`defEqAtP_of_run` fires a recorded comparison only against *both*
sides' gradings.  Every iota walk compares a statement-frame opener's
annotation against a domain of an `instPisAt` run — the recursor's
prefix domains (`rdoms`), the constructor's field domains (`cdoms`),
the rule's λ-domains (`ldomsL`).  The **a**-side is a slot of the
stored `iota_j` theorem's own tower and is graded by `hokA_padded`.
The **b**-side is a slot of a *different* stored type's tower,
instantiated at the statement frame, and nothing in the checker's run
record types it: `checkIotaThm` compares domains with `checkDefEqList`
and never infers them (`Kernel/Modeled.lean:109-135`), so the P tier's
general grading producer — `InferClaims2P` from an `inferTypeCore`
run — has nothing to consume.

So the b-side's grading has to come from its **own type's** tower, and
this file is the lemma that walks it: an `instPisAt` run's domains are
graded whenever the type's reading is, the spine's readings are, and
each spine element's value inhabits the domain it is substituted into.
The last premise is the load-bearing one and is where the walks come
back in — which is why the stage that consumes this runs an induction
on the frame position, spending the equality at position `i` to earn
the grading at position `i + 1`.

**Why the spine premise is cheap where it is used.**  On a `.plain`
fire every spine element is a frame *opener*, and an opener reads to a
`.bvar` (`denoteP_fvar`), which is graded by definition — so the
`AnnotOkP` premise costs nothing there.  On a `.nested` fire the spine
is the instantiated pins, and `RecRuleLawP` already carries their open
readings **graded** (the ratified iota-seal repair, `Annot/EnvS2P.lean`)
— the conjunct that was added for the pins' own sake turns out to be
exactly what this lemma asks for.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AVExpr}

/-! ## The `.pi` split, in the P currency -/

/-- A `.pi` reading's domain is graded when the reading is. -/
theorem AnnotOkP_pi_dom {ρ : Nat → V} {u v : Nat} {A B : AVExpr}
    (h : AnnotOkP V ρ (.pi u v A B)) : AnnotOkP V ρ A :=
  ⟨((AnnotOk2_pi V ρ u v A B) ▸ h.1).1,
    ((AnnotValidV_pi V ρ u v A B) ▸ h.2).1⟩

/-- A `.pi` reading's body is graded at every extension by an element
of the domain. -/
theorem AnnotOkP_pi_body {ρ : Nat → V} {u v : Nat} {A B : AVExpr}
    (h : AnnotOkP V ρ (.pi u v A B)) {x : V}
    (hx : x ∈ˢ interp2 V ρ A) : AnnotOkP V (cons x ρ) B :=
  ⟨((AnnotOk2_pi V ρ u v A B) ▸ h.1).2 x hx,
    ((AnnotValidV_pi V ρ u v A B) ▸ h.2).2.1 x hx⟩

/-! ## The instantiated domains -/

set_option maxHeartbeats 1600000 in
/-- **An `instPisAt` run's domains are graded**, given the type's own
grading, the spine's gradings, and — the load-bearing premise — that
each spine element's value inhabits the domain it goes into.

The induction is the checker's own order: the head domain is the
type's `.pi` domain, and the tail is the run on the β-reduct, whose
reading is the body's reading substituted (`denoteP_beta`) and whose
grading is `AnnotOkP_inst0` at the head membership. -/
theorem instPisAt_domsP_graded {ρ' : Nat → V}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AVExpr) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {D : Nat} {T : AVExpr},
      (∀ (i : Nat) (x : Expr), sp[i]? = some x →
        Expr.WScoped D x ∧ x.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow D ty → ty.looseBVarsBounded 0 = true →
      denoteP acval env φ D ty = some T →
      AnnotOkP V ρ' T →
      (∀ (i : Nat) (x : Expr), sp[i]? = some x →
        ∃ w, denoteP acval env φ D x = some w ∧ AnnotOkP V ρ' w ∧
          ∀ dw, denoteP acval env φ D (ds.getD i default) = some dw →
            interp2 V ρ' w ∈ˢ interp2 V ρ' dw) →
      ∀ (i : Nat), i < sp.length → ∀ dw : AVExpr,
        denoteP acval env φ D (ds.getD i default) = some dw →
        AnnotOkP V ρ' dw := by
  intro sp
  induction sp with
  | nil => intro ty ds rs h D T _ _ _ _ _ _ i hi; exact absurd hi (by simp)
  | cons a sp ih =>
    intro ty ds rs h D T hsp hfb hb hT hokT hmem i hi
    obtain ⟨hwsa, hba⟩ := hsp 0 a rfl
    obtain ⟨w, hw, hokw, hmem0⟩ := hmem 0 a rfl
    match ty, h with
    | .forallE nmT dom body mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hfb' : Expr.fvarsBelow D dom ∧ Expr.fvarsBelow D body := hfb
      have hb' : dom.looseBVarsBounded 0 = true ∧
          body.looseBVarsBounded 1 = true := by
        revert hb
        simp [Expr.looseBVarsBounded]
      rw [denoteP_forallE] at hT
      cases hA : denoteP acval env φ D dom with
      | none => rw [hA] at hT; exact nomatch hT
      | some A => ?_
      rw [hA] at hT
      cases hB : denoteP acval env φ (D + 1)
          (body.instantiate1 (.fvar D nmT dom)) with
      | none => rw [hB] at hT; exact nomatch hT
      | some B => ?_
      rw [hB] at hT
      obtain rfl : T = .pi 0 (pwBit φ mb.pw) A B :=
        (Option.some.inj hT).symm
      have hdom0 : (dom :: p.1).getD 0 default = dom := rfl
      -- the head domain
      have hmemA : interp2 V ρ' w ∈ˢ interp2 V ρ' A :=
        hmem0 A (by rw [hdom0]; exact hA)
      match i with
      | 0 =>
        intro dw hdw
        rw [hdom0, hA] at hdw
        obtain rfl := Option.some.inj hdw
        exact AnnotOkP_pi_dom hokT
      | i + 1 =>
        intro dw hdw
        -- the tail: the run on the β-reduct
        have hTI : denoteP acval env φ D (body.instantiate1 a)
            = some (B.inst w 0) := by
          rw [denoteP_beta hacl hainst (n := nmT) (ty := dom) hfb'.2
            hwsa hba hw 0, hB]
          rfl
        have hokBI : AnnotOkP V ρ' (B.inst w 0) :=
          (AnnotOkP_inst0 hokw).mpr (AnnotOkP_pi_body hokT hmemA)
        refine ih h1
          (fun i0 x hx => hsp (i0 + 1) x (by simpa using hx))
          (Expr.fvarsBelow_instantiate1_gen hwsa.fvarsBelow 0 hfb'.2)
          (Expr.looseBVarsBounded_instantiate1_gen hba hb'.2)
          hTI hokBI ?_ i (by simpa using hi) dw (by simpa using hdw)
        intro i0 x hx
        obtain ⟨w0, hw0, hok0, hm0⟩ := hmem (i0 + 1) x (by simpa using hx)
        exact ⟨w0, hw0, hok0, fun dw0 hdw0 =>
          hm0 dw0 (by simpa using hdw0)⟩

end Setlec.SetR.Interp2
