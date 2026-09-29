module

public import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Rules.Sound
import ConLeche.Model.IndFrame
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.TargetCallMove
import ConLeche.Model.Inductives.TargetCallRead
import ConLeche.Model.Inductives.TargetIhSlot
public import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Semantics.Kit
import ConLeche.Verify.Leaves
import ConLeche.Verify.BetaGate

public section

/-!
# A target call's target at a valuation of the holes

The target check types a recursive call on the member-ABSTRACTED terms
(`targetCallOk`) at the ABSTRACT frame: the rule's frame, the block's
member holes, then the fields again with their annotations abstracted
(`targetAbsFields`, each typed there: `walkCtx_absFields`).  There the
field's abstract type is defeq to `∀ a⃗, hole x⃗ e⃗` (`hdeq`), both sides
inferred (`hfld`, `hwant`).  `targetCall_gen` reads it at any valuation
`hv` of the holes (at their formers' types) that puts every field in
its abstract type's reading (`hii`): the field lies in the Π's reading
(the defeq equates the two readings); read at the copies' own values the
moved terms are the unmoved ones at the holes' frame (`move_read`,
`move_interp`); the Π's body is the hole applied to the parameters and
the index arguments (the abstraction leaves the index arguments alone),
whose grading makes the arguments fit the hole's type's binder data — a
graph's domain is rigid (`spineFit_of_wellDenoted_mkAppN_pi`).

It is stated at a call's typing run (`TargetCallRun`) and the frame's
walk context, generic in everything the rule data pin;
`TargetCallCore.lean` instantiates it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Gen

variable {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat}

/-- The value of a frame variable, read above extra slots. -/
theorem interp_frame_fvar {D E i : Nat} {L : List V} {ρ : Nat → V} {extra : List V}
    (hL : L.length = D) (hE : extra.length = E) (hi : i < D) :
    interp V (consList extra (consList L ρ)) (.bvar (D + E - 1 - i)) = L.getD i pt := by
  rw [interp_bvar, show D + E - 1 - i = (D - 1 - i) + extra.length from by omega,
    consList_apply_add, consList_getD_of_lt _ _ _ (by omega), hL,
    show D - 1 - (D - 1 - i) = i from by omega]


omit [SetTheory V] in
theorem targetAbs_mkAppN {names : List Name} {lvls : List Level} {holes : List Expr} :
    ∀ (as : List Expr) (f : Expr),
      ConLeche.targetAbs names lvls holes (Expr.mkAppN f as)
        = Expr.mkAppN (ConLeche.targetAbs names lvls holes f)
            (as.map (ConLeche.targetAbs names lvls holes))
  | [], _ => rfl
  | a :: as, f => by
    show ConLeche.targetAbs names lvls holes (Expr.mkAppN (.app f a) as) = _
    rw [targetAbs_mkAppN as (.app f a)]
    rfl

omit [SetTheory V] in
theorem teleDoms_length {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}
    {D : Nat} : ∀ (tys os : List Expr) {ds : List AnnotTerm},
      teleDoms acval env φ D os tys = some ds → ds.length = tys.length
  | [], _, ds, h => by simp [teleDoms] at h; subst h; rfl
  | ty :: tys, os, ds, h => by
    simp only [teleDoms, Option.bind_eq_bind] at h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := (Option.some.inj h).symm
    simp [teleDoms_length tys _ hr]


/-- Every subject of a read spine reads. -/
theorem spine_reads {d : Nat} :
    ∀ {es : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine mT.acval envT φ d es vs →
      ∀ e ∈ es, ∃ a, denoteMeta mT.acval envT φ d e = some a
  | _, _, .nil, _, he => nomatch he
  | _, _, .cons (a := a0) ha hr, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, ha⟩
    · exact spine_reads hr e he

/-- A read spine's values, entry by entry. -/
theorem spine_map_getD {d : Nat} {τ : Nat → V} :
    ∀ {es : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine mT.acval envT φ d es vs →
      vs.map (interp V τ)
        = es.map fun e => interp V τ ((denoteMeta mT.acval envT φ d e).getD default)
  | _, _, .nil => rfl
  | _, _, .cons ha hr => by
    simp only [List.map_cons, ha, Option.getD_some]
    rw [spine_map_getD hr]

/-! ## The call's shape, from the abstraction -/

omit [SetTheory V] in
/-- In a duplicate-free list, an entry is found at its own position. -/
theorem findIdx?_of_nodup {l : List Name} (hnd : l.Nodup) {t : Nat} {a : Name}
    (h : l[t]? = some a) : l.findIdx? (· == a) = some t := by
  obtain ⟨ht, hget⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨ht, by simp [hget], fun j hj => ?_⟩
  have hne : l[j] ≠ l[t] := fun he => by
    have := (List.getElem_inj hnd).mp he
    omega
  simpa [hget] using hne

end Gen

end ConLeche.Model
