module

import ConLeche.Model.Inductives.FixRecReadDefs
public import ConLeche.Model.Inductives.FixChainFacts
import ConLeche.Model.Inductives.SumRecFrames
import ConLeche.Semantics.Tower.FixSquashI
import ConLeche.Kernel.PropWhen
import ConLeche.Model.Inductives.FixIntro
public section

/-!
# The recursive recursor's rule law, at the readings (task #188)

The sum route's `sumRecLawCore` (`SumRecLawP.lean`) for the recursive
route: at a frame where the recursor's arguments fit its binder data
and the constructor's arguments fit the constructor's, the recursor at
the constructor value is the rule's right-hand side — the minor at the
fields and at the inductive hypotheses — at the block's arguments and
the fields.  The inductive hypotheses in the rule (`ihAppAV`) read to
the recursor at the block, the field's index values and the field,
exactly the recursor's iota (`nativeRecAVI_iota`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The rule's ih applications at the re-bit telescopes (task #202 A2) -/

/-- An application spine over a function whose reading is the point is
graded whenever the head and the arguments are: the `.app` clause is
witnessed at bit `0` by the singleton of the argument's reading. -/
theorem mkAppN_wellDenotedV_of_pt :
    ∀ {f : AnnotTerm} {args : List AnnotTerm} {ρ : Nat → V},
      WellDenotedV V ρ f → interp V ρ f = (pt : V) →
      (∀ a ∈ args, WellDenotedV V ρ a) →
      WellDenotedV V ρ (AnnotTerm.mkAppN f args)
  | _, [], _, hf, _, _ => hf
  | f, a :: args, ρ, hf, hpt, hargs => by
    rw [AnnotTerm.mkAppN_cons]
    have ha := hargs a List.mem_cons_self
    refine mkAppN_wellDenotedV_of_pt (f := .app f a) ?_ ?_
      (fun b hb => hargs b (List.mem_cons_of_mem _ hb))
    · refine ⟨⟨hf.1, ha.1, 0, image (fun _ => interp V ρ a) unitSet, fun _ => unitSet, ?_, ?_, ?_⟩,
        hf.2, ha.2⟩
      · rw [hpt]; exact pt_mem_piR_zero_of fun _ _ => pt_mem_unitSet
      · exact mem_image.mpr ⟨pt, pt_mem_unitSet, rfl⟩
      · intro _ _ _; rw [← univ_zero]; exact unitSet_mem_univ 0
    · rw [interp_app, hpt, app_pt]

end ConLeche.Model
