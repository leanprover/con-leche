module

import ConLeche.Model.Annot.Valid
import ConLeche.Semantics.Tower.SumTower
import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Model.Annot.LfpFormer
public import ConLeche.Model.Inductives.ClassGenStep
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Inductives.BlockData
import ConLeche.Verify.Abstract
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.StoredShapes
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Semantics.Kit
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitInst

public section

/-!
# The minor premise's own typing, from the generator (`hminor`, G1-syn)

`genHstep` (`ClassGenStep.lean`) proves the step's typing at the
generated family from the MINOR PREMISE's typing, stated semantically
(`hminor`): a minor applied to fields fitting the rule frame's field
domains and to `ih` values of the `ih` binders' types
(`genIhDomAV`) lands in the motive at the constructor.  Here that
statement is DERIVED from the generator, and so are the rule frame's
components themselves — the field domains, the `ih` data, the
conclusion's index spine and constructor term — as the pieces of the
minor premise's domain in the generated type's reading (finding 3 of
CLASSCHECK / G1-SYN).

The minor sits in the shared prefix at position `mp = nP + s`, so its
domain is read at depth `mp`; the rule frame is at depth `rP` (the whole
prefix).  The reading is peeled at `mp`, where the generator's own
`closeTelescope` lives (so the opened pieces are the raw pieces, up
to erasure — the type is stored as generated), and moved to `rP` by the de Bruijn lift over the
`rP - mp` later prefix binders (`denoteMeta_lift` on the model side is
free: `stripPisAV` of a lifted reading is the lifted pieces).  Three
readings of openings at different depths meet:

* a FIELD domain `k` is read at `mp + k` and lifted at cutoff `k`;
* an `ih` domain `l` is read at `mp + nF + l`, under the `l` earlier
  `ih` binders — but it names no `ih` variable (the generator closes the
  `ih`'s own telescope again, `ClassGen.minorTy_spec`), so its reading is
  the lift by `l` of its reading at `mp + nF`, which is then lifted to
  `rP + nF`: that is `genIhDomAV (rP + nF) mt q` for the `ih` datum `q`
  read off it;
* the CONCLUSION is read at `mp + nF + nIh`, again the lift of its
  reading at `mp + nF` (it names no `ih` variable either).

The binders' bits are never inspected: the generated type's reading is
bit-VALID (`AnnotValid`, the inference claim's currency), and validity
descends the prefix to the minor's domain, whose Π-tower then applies
(`foldl_app_mem_mkPisAV`).  What the components are asked to be for the
chain independence rows (`genHchI_of_readings`, `ihDatumBelow_of_readings`)
is only their `bvarsBelow` bound; the lifted readings have it (they are
not themselves readings of a scoped term at `rP`: the opened pieces at
`rP` are the generator's pieces RENAMED, which the proof never needs).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ClassGen ClassGenScoped ClassCtor ScB closeTelescope
  classGenRecTy classBinder)

universe w

/-! ## De Bruijn bookkeeping on readings -/

/-! ## Frames -/

section Frames

variable {V : Type w} [SetTheory V]

/-- **Lifting over the top of the outer spine**: the frame
`ys` over `zs` read through a lift by `n` at `|ys|` is the frame `ys`
over `zs` without its last `n` values. -/
theorem shiftE_consList {n k : Nat} {ys zs : List V} {ρ : Nat → V} (hk : ys.length = k)
    (hn : n ≤ zs.length) :
    shiftE n k (consList ys (consList zs ρ))
      = consList ys (consList (zs.take (zs.length - n)) ρ) := by
  funext i
  simp only [shiftE]
  split
  · rw [consList_getD_of_lt ys _ i (by omega), consList_getD_of_lt ys _ i (by omega)]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + k := ⟨i - k, by omega⟩
    subst hk
    rw [show j + ys.length + n = (j + n) + ys.length by omega, consList_apply_add,
      consList_apply_add]
    have hdl : (zs.drop (zs.length - n)).length = n := by simp; omega
    rw [show consList zs ρ = consList (zs.drop (zs.length - n)) (consList (zs.take (zs.length - n)) ρ)
      by rw [← consList_append, List.take_append_drop]]
    have := consList_apply_add (zs.drop (zs.length - n)) (consList (zs.take (zs.length - n)) ρ) j
    rw [hdl] at this
    exact this

omit [SetTheory V] in
/-- Lifting over a whole spine forgets it. -/
theorem shiftE_zero_consList {n : Nat} {ys : List V} {σ : Nat → V} (hn : ys.length = n) :
    shiftE n 0 (consList ys σ) = σ := by
  funext i
  subst hn
  simp only [shiftE, Nat.not_lt_zero, if_false]
  exact consList_apply_add ys σ i

omit [SetTheory V] in
theorem take_append_of_le {xs ys : List V} {n : Nat} (h : n ≤ xs.length) :
    (xs ++ ys).take n = xs.take n := by
  rw [List.take_append_of_le_length h]

end Frames

/-! ## Validity along a Π-tower -/

section Valid

variable {V : Type w} [SetTheory V]

/-- A valid Π-tower's domains are valid at a fitting spine's prefixes. -/
theorem annotValid_piDom_at {B : AnnotTerm} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {bs : List V},
      AnnotValid V ρ (mkPisAV tl B) → SpineFit ρ (tl.map (·.2.2)) bs →
      ∀ l, l < tl.length →
        AnnotValid V (consList (bs.take l) ρ) ((tl.map (·.2.2)).getD l default)
  | [], _, _, _, _, l, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, _, [], _, h, _, _ => h.elim
  | d :: tl, ρ, b :: bs, hv, h, l, hl => by
    have hv' : AnnotValid V ρ (.pi d.1 d.2.1 d.2.2 (mkPisAV tl B)) := hv
    rw [AnnotValid_pi] at hv'
    cases l with
    | zero => simpa using hv'.1
    | succ l =>
      simp only [List.map_cons, List.getD_cons_succ, List.take_succ_cons, consList_cons]
      exact annotValid_piDom_at (hv'.2.1 b h.1) h.2 l (by simpa using hl)

end Valid

/-! ## Bounds of lifted pieces -/

/-! ## Readings of a variable spine -/

/-! ## The minor premise's typing -/

/-- The prefix position of class `t`'s motive. -/
@[expose] def classMotPos (g : ClassGen) (t : Nat) : Nat :=
  g.nP + (ConLeche.ClassRead.motiveSlot ⟨g.slots, []⟩ t).getD 0

end ConLeche.Model
