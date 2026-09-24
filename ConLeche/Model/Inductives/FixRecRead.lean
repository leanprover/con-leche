module

public import ConLeche.Model.Inductives.FixRecReadDefs
public import ConLeche.Verify.Inductives.FixRec
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitRename
public section

/-!
# The generated recursive recursor's readings (task #188)

`ConLeche/Model/Inductives/SumRecRead.lean` with the inductive hypotheses:
the generated recursive recursor type reads to the Π-tower over
`fixRecDataAV` and rule `j` to the λ-tower over `fixRuleDataAV`
(`ConLeche/Model/Inductives/FixRecReadDefs.lean`).

The one genuinely new reading is the `ih` binder's domain
`∀ a⃗, motive e⃗_i(a⃗) (f_i a⃗)`.  A recursive field's own telescope and
its domain's index expressions are read at the constructor's OWN
opening — the parameters, the `i` earlier fields, then the telescope's
own openers (`FieldReadAt`, off `CtorReadR` by `fieldReadAt_of`) —
while the recursor's frame puts the fields `o` slots higher (the
motive and the earlier minors sit between) and `nF - i + l` binders
above.  Moving between the two frames is `Expr.shiftFrom` iterated
(`denoteMeta_instSeq_shift`), twice: once to insert the fields and the
earlier hypotheses below the field's own frame, once to insert the
`o` extras between the parameters and the fields — precisely
`ihIdxAtM`'s two lifts, the telescope's openers staying innermost
(task #202).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## Reading through an inserted block of variables -/

/-- **`denoteMeta_shiftFrom`, iterated**: inserting `o` fresh variable
slots at index `p` lifts the reading by `o` at the cut `d - p`. -/
theorem denoteMeta_shiftFromN {acval : Name → (Name → Nat) → AnnotTerm}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {p : Nat} :
    ∀ (o : Nat) {e : Expr} {d : Nat}, p ≤ d → Expr.WScoped d e →
      denoteMeta acval env φ (d + o) (Expr.shiftFromN p o e)
        = (denoteMeta acval env φ d e).map (AnnotTerm.liftN o · (d - p))
  | 0, e, d, _, _ => by
    show denoteMeta acval env φ (d + 0) e = _
    rw [Nat.add_zero]
    cases denoteMeta acval env φ d e with
    | none => rfl
    | some v => simp only [Option.map_some, AnnotTerm.liftN_zero]
  | o + 1, e, d, hpd, hw => by
    show denoteMeta acval env φ (d + (o + 1)) (Expr.shiftFrom p (Expr.shiftFromN p o e)) = _
    rw [show d + (o + 1) = d + o + 1 from by omega,
      denoteMeta_shiftFrom hacl _ (d + o) (by omega) (Expr.WScoped_shiftFromN o hw),
      denoteMeta_shiftFromN hacl o hpd hw]
    cases denoteMeta acval env φ d e with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Option.some.injEq]
      exact AVExprSubst.liftN_liftN_absorb v (by omega) (by omega) 1

/-! ## Spine bookkeeping -/

/-- A read spine, re-read entry by entry at another frame. -/
theorem DenoteMetaSpine.map_map {acval : Name → (Name → Nat) → AnnotTerm} {d d' : Nat}
    {f g : Expr → Expr} {h : AnnotTerm → AnnotTerm} :
    ∀ {as : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d (as.map f) vs →
      (∀ (a : Expr) (v : AnnotTerm), a ∈ as → denoteMeta acval env φ d (f a) = some v →
        denoteMeta acval env φ d' (g a) = some (h v)) →
      DenoteMetaSpine acval env φ d' (as.map g) (vs.map h)
  | [], vs, hsp, _ => by
    cases hsp
    exact .nil
  | a :: as, vs, hsp, hfg => by
    rw [List.map_cons] at hsp
    cases hsp with
    | cons hd htl =>
      exact .cons (hfg a _ List.mem_cons_self hd)
        (DenoteMetaSpine.map_map htl fun x v hx hv => hfg x v (List.mem_cons_of_mem _ hx) hv)

/-! ## Frames of the same variables -/

/-! ## The `ih` binders' index expressions -/

/-! ## The recursor's frame, variable by variable -/

/-! ## Telescopes, read binderwise -/

/-! ## Π- and λ-towers over a frame -/

/-! ## The `ih` binders -/

end ConLeche.Model
