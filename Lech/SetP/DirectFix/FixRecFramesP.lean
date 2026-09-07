import Lech.SetP.DirectFix.FixRecReadDefsP
import Lech.SetP.DirectFix.FixRealChainsP
import Lech.SetP.DirectSum.SumRecFramesP
import Lech.Semantics.Tower.FixRecI

/-!
# The recursive recursor's K-frames, part 1: the ih tower read (task #188)

The inductive-hypothesis binders of a minor (`ihPisAV`,
`FixRecReadDefsP.lean`) read, at a field frame over the K-frame, to
the ih tower `ihSpL` (`Lech/Semantics/Tower/FixCaseI.lean`) over the
ih domains `ihDomsI` — the motive at the recursive field's index
readings and the field.  With it, a recursive minor's reading is the
minor space with ih-extended conclusions (`interp_minorSpI_of_tele`
with the ih tower as the conclusion).
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The kernel's recursive positions -/

omit [SetTheory V] in
/-- The kernel's recursive-position list is the semantic one. -/
theorem recIdx_rsOf (ks : List RecFieldKind) : recIdx (rsOf ks) ks.length = Lech.recIdxOf ks := by
  unfold recIdx Lech.recIdxOf
  apply List.filter_congr
  intro i hi
  rw [List.mem_range] at hi
  rw [rsOf_getD hi]
  cases ks.getD i .ordinary <;> simp

/-! ## The ih domain, read -/

omit [SetTheory V] in
/-- The field frame over a K-frame: `l` ih values over the `nF`
fields over the `o - 1` minors and the motive over the parameter
frame.  The frame `o` below the fields is the parameter frame. -/
theorem shiftE_fieldFrame {o : Nat} {ρp : Nat → V} {M : V} {ms : List V} (hms : ms.length + 1 = o)
    (fs ihs : List V) :
    shiftE o (fs.length + ihs.length) (consList ihs (consList fs (consList ms (cons M ρp)))) = consList ihs (consList fs ρp) := by
  rw [← consList_append, ← List.length_append, shiftE_consList_len, ← hms,
    shiftE_consList_add, shiftE_succ_cons, shiftE_zero_zero, consList_append]

/-- Field `i`'s index expression, moved to the ih binder's frame, reads
at the field's own frame. -/
theorem interp_ihIdxAt {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) (E : AVExpr) :
    interp2 V (consList ihs (consList fs (consList ms (cons M ρp)))) (ihIdxAt nF o i l E)
      = interp2 V (consList (fs.take i) ρp) E := by
  unfold ihIdxAt
  rw [interp2_liftN, show nF + l = fs.length + ihs.length from by omega, shiftE_fieldFrame hms,
    interp2_liftN, ← consList_append]
  have hsplit : fs ++ ihs = fs.take i ++ (fs.drop i ++ ihs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, consList_append, show nF - i + l = (fs.drop i ++ ihs).length from by
    rw [List.length_append, List.length_drop]; omega, shiftE_consList]

/-- The ih domain reads to the motive at the field's index values and
the field. -/
theorem interp_ihDomAV {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i < nF) (Eis : List AVExpr) :
    interp2 V (consList ihs (consList fs (consList ms (cons M ρp)))) (ihDomAV nF o i l Eis)
      = SetTheory.app ((Eis.map (interp2 V (consList (fs.take i) ρp))).foldl SetTheory.app M)
          (fs.getD i pt) := by
  unfold ihDomAV
  rw [AVExpr.mkAppN_append_one, interp2_app, interp2_mkAppN, interp2_bvar, interp2_bvar,
    ← List.foldl_map (f := interp2 V (consList ihs (consList fs (consList ms (cons M ρp)))))
      (g := SetTheory.app), List.map_map]
  have hM : consList ihs (consList fs (consList ms (cons M ρp))) (nF + o - 1 + l) = M := by
    rw [show nF + o - 1 + l = (nF + o - 1) + ihs.length from by omega, consList_apply_add,
      show nF + o - 1 = (o - 1) + fs.length from by omega, consList_apply_add,
      show o - 1 = 0 + ms.length from by omega, consList_apply_add]
    rfl
  have hf : consList ihs (consList fs (consList ms (cons M ρp))) (nF - 1 - i + l) = fs.getD i pt := by
    rw [show nF - 1 - i + l = (nF - 1 - i) + ihs.length from by omega, consList_apply_add,
      consList_apply_lt' fs _ (by omega), show fs.length - 1 - (nF - 1 - i) = i from by omega]
  rw [hM, hf]
  congr 2
  apply List.map_congr_left
  intro E _
  simp only [Function.comp]
  exact interp_ihIdxAt hms hfs hihs (Nat.le_of_lt hi) E

/-! ## The ih tower, read -/

/-- **The ih binders read to the ih tower** over the ih domains, the
body under them reading to the conclusion. -/
theorem interp_ihPisAV {ℓ b nF o : Nat} (hbz : ℓ = 0 ↔ b = 0) {ρp : Nat → V} {M : V}
    {ms : List V} (hms : ms.length + 1 = o) {fs : List V} (hfs : fs.length = nF)
    {Eiss : List (List AVExpr)} {C : V} :
    ∀ (is : List Nat) (l : Nat) (ihs : List V) (body : AVExpr),
      ihs.length = l → (∀ i ∈ is, i < nF) →
      (∀ ihs' : List V, ihs'.length = l + is.length →
        interp2 V (consList ihs' (consList fs (consList ms (cons M ρp)))) body = C) →
      interp2 V (consList ihs (consList fs (consList ms (cons M ρp)))) (ihPisAV nF o b Eiss is l body)
        = ihSpL ℓ C (is.map fun i =>
            SetTheory.app (((Eiss.getD i []).map (interp2 V (consList (fs.take i) ρp))).foldl
              SetTheory.app M) (fs.getD i pt))
  | [], l, ihs, body, hihs, _, hbody => by
    simp only [ihPisAV, List.map_nil, ihSpL]
    exact hbody ihs (by simp [hihs])
  | i :: is, l, ihs, body, hihs, hlt, hbody => by
    simp only [ihPisAV, List.map_cons, ihSpL, interp2_pi]
    rw [piR_congr_bit (v := b) (v' := ℓ) hbz.symm,
      interp_ihDomAV hms hfs hihs (hlt i List.mem_cons_self)]
    apply piR_congr
    intro x _
    rw [consList_snoc']
    refine interp_ihPisAV hbz hms hfs is (l + 1) (ihs ++ [x]) body (by simp [hihs])
      (fun i' hi' => hlt i' (List.mem_cons_of_mem _ hi')) ?_
    intro ihs' hl
    exact hbody ihs' (by rw [hl, List.length_cons]; omega)

end Lech.SetP
