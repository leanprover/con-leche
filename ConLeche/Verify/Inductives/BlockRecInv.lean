module

public import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Verify.Subst
import ConLeche.Verify.InstList
import ConLeche.Verify.InstSpine

public section

/-!
# The recursor CHECK at k members, inverted

What `ConLeche/Kernel/Inductives/BlockRec.lean`'s pieces are, said in
the form the model tier reads them:

* the **guarded call's characterisation** (`IhCallRun`, `blockIhCall?_run`): a
  node the abstraction replaces IS the generated recursive call
  `rec_{c'} x⃗ e⃗_i(a⃗) (f_i a⃗)` at its own arguments, on a field of
  THIS constructor whose kind names the member `rec_{c'}` eliminates,
  exactly as terms (see the lemma's docstring for why not up to
  `Expr.resetMeta`);
* the **abstraction's equations** (`abstractIh_*`);
* the recursor stage's NAME checks, the counting and pin halves of the
  elimination guard, and the two capture-avoiding
  substitutions at bvar-closed arguments.

## The rule check's two ENVIRONMENT claims (G1, G2)

Two facts about `checkBlockRule`
(`ConLeche/Kernel/Inductives/BlockInstall.lean`) that the model's
typing consumer needs by name.  The stage is handed `opsR`/`envR` for
the ANNOTATION and `opsT`/`envT` for both of these, and
`checkBlockRecK` instantiates `envT` with the CONSTRUCTORS'
environment — the one it was called at, before `consBlockRecsBare`.

* **G1 — the abstracted residue is typed at `envT`.**
  `opsT.inferType envT depth bodyO` and
  `opsT.isDefEq envT depth tyB <the recursor's own conclusion at the
  rule's prefix, the constructor's indices and `C_J p⃗ f⃗`>` run at the
  constructors' environment, NOT at the one holding the `k` rule-less
  recursors.  The residue and its whole opened frame (the recursor's
  own prefix, the fields, the `ih` openers) are recursor-free by
  construction (the abstraction replaces every guarded call and fails
  at any other recursor constant, `abstractIh_const`), and a model of an environment holding the
  recursors would owe every constant's leaf a type, the recursors'
  being the recursion theorem the certificate is feeding.  The
  annotation stays at `envR`: a rule mentions the recursors, and its
  annotate-claims are not consumable at any model for the same
  reason.

* **G2 — the rule's λ-domains are compared BINDER BY BINDER** with the
  opened STORED recursor type's frame:
  `checkDefEqList opsT envT (rP+nF) ((fvsPref ++ fvsF).map
  Expr.fvarTypeD) ldoms`, where `ldoms` comes from
  `Expr.instLamsAt (fvsPref ++ fvsF) rhsA` — `checkIotaRule`'s move
  (`ConLeche/Kernel/Inductives/Modeled.lean`).  Stage (b)'s whole-type
  `isDefEq` compares two CLOSED Π-types and does not give per-binder
  equality of their readings: at `ℓ = 0` both read to a truth value,
  and at `ℓ ≠ 0` an empty fibre makes two Π-readings agree at
  different domains.  The STORED right-hand side is the annotated
  STREAM one, whose λ-tower the ι step applies at frames of the
  STORED type, so the model must read those binders.

What is NOT here, and is the semantics tier's (design §4.3): the
abstraction's own INVERSE, `body = body''[ih_i a⃗ ↦ spine]`.  Its
syntactic half is `blockIhCall?_run` (every replaced node is the
spine); the substitution lemma is stated over the DENOTATION
(`interp_instsAV`, `Semantics/Tower/BlockRecI.lean`).
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

open Expr

/-! ## The guarded recursive call -/

/-! ## The abstraction -/

/-! ## Stage (a)'s two NAME checks, exposed

`checkBlockRecPins` refuses a recursor named for one of the constants
the environment's own guards look up (`reservedRecName`) and a
block whose recursor names are not, as a SET, official's
`{T_m.rec | m a member}`.  The first is what the MODEL consumes — it
makes `natLitSupported` and `strLitSupported` congruent across the
recursors' cons (`strLitSupported_consBlockRecs`,
`ConLeche/Verify/Inductives/BlockWF.lean`); the second has no model
consumer at all (it only shrinks the accept set) and is exposed here
so that what the stage guarantees about names is read in ONE place. -/

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
theorem checkBlockRecSmallElim_inv {p : BlockShape} {nested : Bool} {us : List Level}
    (h : checkBlockRecSmallElim (m := CheckM) p nested us = .ok ()) :
    0 < p.k ∧ (blockLargeElimAllowed p nested = true ∨
      ∀ u ∈ us, Level.isEquiv u Level.zero = some true) := by
  rw [checkBlockRecSmallElim] at h
  split at h
  · next hk =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · next hc =>
      refine ⟨hk, ?_⟩
      simp only [Bool.or_eq_true] at hc
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
  split at h
  · next hall => exact fun u hu => eq_of_beq (List.all_eq_true.mp hall u hu)
  · exact nomatch h

/-! ## The two capture-avoiding substitutions, at bvar-closed arguments

`blockIhCall?`, `blockIhPis` and `checkBlockRule`'s conclusion are all
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
