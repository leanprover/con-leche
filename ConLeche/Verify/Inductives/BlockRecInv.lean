module

public import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Verify.Subst
import ConLeche.Verify.InstList
import ConLeche.Verify.InstSpine

public section

/-!
# The recursor stage's shared inversions

The counting and pin halves of the elimination guard
(`checkBlockRecSmallElim`, `checkBlockRecElimPin`,
`Kernel/Inductives/BlockInstall.lean`), which the target check runs on
its family, and the two capture-avoiding substitutions at bvar-closed
arguments.  The check's own run records are
`Verify/Inductives/RecCheckRun.lean`; its kind-free facts, the record the
model reads, `Verify/Inductives/RecStage.lean`.
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

open Expr

/-! ## The COUNTING half of the elimination guard

`checkBlockRecSmallElim` (`Kernel/Inductives/BlockInstall.lean`) is the
one clause of official's `elim_only_at_universe_zero` the model reads
in the LEVEL currency instead of through a run: at a block whose result
sort may be `0`, a family of more than one member eliminates only at a
level equivalent to zero.  Its inversion is the whole content. -/

/-- **The counting guard, exposed**: a block declares a family, and
either a large eliminator is ALLOWED on it (`blockLargeElimAllowed`,
whose four facts `blockLargeElim_counting` reads off at a `Prop` result
sort) or every recursor eliminates at a level `Level.isEquiv` to
zero. -/
theorem checkBlockRecSmallElim_inv {p : BlockShape} {nested licensed : Bool}
    {us : List Level}
    (h : checkBlockRecSmallElim (m := CheckM) p nested licensed us = .ok ()) :
    0 < p.k ∧ ((blockLargeElimAllowed p nested = true ∧ licensed = true) ∨
      ∀ u ∈ us, Level.isEquiv u Level.zero = some true) := by
  rw [checkBlockRecSmallElim] at h
  split at h
  · next hk =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · next hc =>
      refine ⟨hk, ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
      rcases hc with hc | hc
      · exact .inl hc
      · exact .inr fun u hu => eq_of_beq (List.all_eq_true.mp hc u hu)
    · exact nomatch h
  · exact nomatch h

/-- **The elimination-level PIN, exposed**: every recursor's checked
conclusion sort is equivalent to `structElimLevel p.elim p.large` — the
level the rule frame's `PropWhen` datum is computed from. -/
theorem checkBlockRecElimPin_inv {p : BlockShape} {us : List Level}
    (h : checkBlockRecElimPin (m := CheckM) p us = .ok ()) :
    ∀ u ∈ us, Level.isEquiv u (structElimLevel p.elim p.large) = some true := by
  rw [checkBlockRecElimPin] at h
  cases ho : Level.isEquivList us (us.map fun _ => structElimLevel p.elim p.large) with
  | none => rw [ho] at h; exact nomatch h
  | some b =>
    rw [ho] at h
    cases b with
    | false => exact nomatch h
    | true => exact Level.isEquivList_map_const ho

/-! ## The two capture-avoiding substitutions, at bvar-closed arguments

`targetIhTy`, `targetCallOk` and `targetRule`'s conclusion are all
built with `Expr.instPisAtLift`, and the ih telescope is opened with
`Expr.instantiateList`; neither has a reading lemma, because both are
written for arguments that may mention the ambient binders.  **At
arguments that are bvar-closed — which is what they are once the rule
body is OPENED, the frame `denoteMeta` reads at — both collapse onto
operations the model already owns**: `instPisAtLift` onto `instPisAt`
(nothing to lift, `instantiate1Lift_eq_instantiate1`), and
`instantiateList` onto `instSeq` (through `instSpine`).  These are the
two syntactic halves of the batteries the model tier needs. -/

/-- **`instPisAtLift` is `instPisAt` at bvar-closed arguments.** -/
theorem instPisAtLift_eq_instPisAt :
    ∀ {as : List Expr} {t : Expr}, (∀ a ∈ as, a.looseBVarsBounded 0 = true) →
      Expr.instPisAtLift as t = (Expr.instPisAt as t).map (·.2) := by
  intro as
  induction as with
  | nil => intro t _; rfl
  | cons a as ih =>
    intro t h
    cases t with
    | forallE dom body bi =>
      rw [Expr.instPisAtLift, Expr.instPisAt,
        Expr.instantiate1Lift_eq_instantiate1 (h a List.mem_cons_self) body 0,
        ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
      cases Expr.instPisAt as (body.instantiate1 a) <;> rfl
    | _ => rfl

/-- **`instantiateList` is `instSeq` on the reversed list.**  The
`denoteMeta` battery for `instSeq` (`denoteMeta_openRev`) therefore
covers the ih telescope's opening. -/
theorem instantiateList_eq_instSeq {vs : List Expr} (hne : vs ≠ []) (e : Expr) :
    e.instantiateList vs 0 = Expr.instSeq vs.reverse (vs.length - 1) e := by
  have hlen : vs.reverse.length = (vs.length - 1) + 1 := by
    rw [List.length_reverse]
    cases vs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  rw [← Expr.instSpine_eq_instSeq,
    Expr.instSpine_eq_instantiateList vs.reverse (vs.length - 1) e hlen,
    List.reverse_reverse]

end ConLeche
