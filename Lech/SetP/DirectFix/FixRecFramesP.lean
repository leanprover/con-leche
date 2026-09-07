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

/-- `ihIdxAtM` under `as` telescope values reads the field's
expression at the field's own frame under those values. -/
theorem interp_ihIdxAtM {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) (as : List V) (E : AVExpr) :
    interp2 V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l as.length E)
      = interp2 V (consList as (consList (fs.take i) ρp)) E := by
  unfold ihIdxAtM
  rw [interp2_liftN, show nF + l + as.length = as.length + (fs.length + ihs.length) from by omega,
    shiftE_consList_len', shiftE_fieldFrame hms, interp2_liftN, shiftE_consList_len,
    ← consList_append]
  have hsplit : fs ++ ihs = fs.take i ++ (fs.drop i ++ ihs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, consList_append, show nF - i + l = (fs.drop i ++ ihs).length from by
    rw [List.length_append, List.length_drop]; omega, shiftE_consList]

/-- The nested product over the moved telescope at the ih frame is
the nested product over the telescope at the field's own frame. -/
theorem piTele_ihTeleAtGo {v : Nat} {B : List V → V} {nF o i l : Nat} {ρp : Nat → V} {M : V}
    {ms : List V} (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF)
    (hihs : ihs.length = l) (hi : i ≤ nF) :
    ∀ (tl : List (Nat × Nat × AVExpr)) (as acc : List V),
      piTele v (teleOfFields (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
          ((ihTeleAtGo nF o i l as.length tl).map (·.2.2))) B acc
        = piTele v (teleOfFields (consList as (consList (fs.take i) ρp)) (tl.map (·.2.2))) B acc
  | [], _, _ => rfl
  | d :: tl, as, acc => by
    show piTele v (teleOfFields _
      (((d.1, d.2.1, ihIdxAtM nF o i l as.length d.2.2) :: ihTeleAtGo nF o i l (as.length + 1) tl).map
        (·.2.2))) B acc = _
    rw [List.map_cons, List.map_cons]
    simp only [teleOfFields, piTele]
    rw [interp_ihIdxAtM hms hfs hihs hi]
    refine piR_congr fun a _ => ?_
    have := piTele_ihTeleAtGo (v := v) (B := B) (M := M) (ρp := ρp) hms hfs hihs hi tl (as ++ [a])
      (acc ++ [a])
    rw [length_snoc', ← consList_snoc', ← consList_snoc'] at this
    exact this

/-- The ih domain reads to the nested product over the field's
telescope of the motive at the field's index values and the field
applied to the telescope's values (a finitary field: the motive at
the index values and the field). -/
theorem interp_ihDomAV {ℓ nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i < nF) {tl : List (Nat × Nat × AVExpr)} (hbits : ∀ d ∈ tl, (d.2.1 = 0 ↔ ℓ = 0))
    (Eis : List AVExpr) :
    interp2 V (consList ihs (consList fs (consList ms (cons M ρp)))) (ihDomAV nF o i l tl Eis)
      = piTele ℓ (teleOfFields (consList (fs.take i) ρp) (tl.map (·.2.2)))
          (fun as => SetTheory.app
            ((Eis.map (interp2 V (consList as (consList (fs.take i) ρp)))).foldl SetTheory.app M)
            (as.foldl SetTheory.app (fs.getD i pt))) [] := by
  unfold ihDomAV
  rw [Lech.Semantics.interp_mkPisAV_piTele (v := ℓ) (acc := [])
    (B := fun as => SetTheory.app
      ((Eis.map (interp2 V (consList as (consList (fs.take i) ρp)))).foldl SetTheory.app M)
      (as.foldl SetTheory.app (fs.getD i pt)))]
  · have hT := piTele_ihTeleAtGo (v := ℓ) (M := M) (ρp := ρp)
      (B := fun as => SetTheory.app
        ((Eis.map (interp2 V (consList as (consList (fs.take i) ρp)))).foldl SetTheory.app M)
        (as.foldl SetTheory.app (fs.getD i pt))) hms hfs hihs (Nat.le_of_lt hi) tl [] []
    simp only [List.length_nil, consList] at hT
    exact hT
  · intro d hd
    obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hd
    rw [he]; exact hbits d' hd'
  · intro as hsp
    have hlen : as.length = tl.length := by
      rw [hsp.length_eq, List.length_map, ihTeleAtR_length]
    rw [List.nil_append, ← hlen, AVExpr.mkAppN_append_one, interp2_app, interp2_mkAppN,
      interp2_bvar, interp2_mkAppN, interp2_bvar,
      ← List.foldl_map (f := interp2 V (consList as (consList ihs (consList fs (consList ms (cons M ρp))))))
        (g := SetTheory.app) (l := Eis.map (ihIdxAtM nF o i l as.length)),
      ← List.foldl_map (f := interp2 V (consList as (consList ihs (consList fs (consList ms (cons M ρp))))))
        (g := SetTheory.app) (l := teleVarsAV as.length), List.map_map]
    have hM : consList as (consList ihs (consList fs (consList ms (cons M ρp))))
        (nF + o - 1 + l + as.length) = M := by
      rw [consList_apply_add, show nF + o - 1 + l = (nF + o - 1) + ihs.length from by omega,
        consList_apply_add, show nF + o - 1 = (o - 1) + fs.length from by omega, consList_apply_add,
        show o - 1 = 0 + ms.length from by omega, consList_apply_add]
      rfl
    have hf : consList as (consList ihs (consList fs (consList ms (cons M ρp))))
        (nF - 1 - i + l + as.length) = fs.getD i pt := by
      rw [consList_apply_add, show nF - 1 - i + l = (nF - 1 - i) + ihs.length from by omega,
        consList_apply_add, consList_apply_lt' fs _ (by omega),
        show fs.length - 1 - (nF - 1 - i) = i from by omega]
    have hvars : (teleVarsAV as.length).map
        (interp2 V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))) = as :=
      map_fieldBvars_interp rfl _
    rw [hM, hf, hvars]
    congr 2
    apply List.map_congr_left
    intro E _
    simp only [Function.comp]
    exact interp_ihIdxAtM hms hfs hihs (Nat.le_of_lt hi) as E

/-! ## The ih tower, read -/

/-- **The ih binders read to the ih tower** over the ih domains, the
body under them reading to the conclusion. -/
theorem interp_ihPisAV {ℓ b nF o : Nat} (hbz : ℓ = 0 ↔ b = 0) {ρp : Nat → V} {M : V}
    {ms : List V} (hms : ms.length + 1 = o) {fs : List V} (hfs : fs.length = nF)
    {tls : List (List (Nat × Nat × AVExpr))} {Eiss : List (List AVExpr)} {C : V} :
    ∀ (is : List Nat) (l : Nat) (ihs : List V) (body : AVExpr),
      ihs.length = l → (∀ i ∈ is, i < nF) →
      (∀ i ∈ is, ∀ d ∈ tls.getD i [], (d.2.1 = 0 ↔ ℓ = 0)) →
      (∀ ihs' : List V, ihs'.length = l + is.length →
        interp2 V (consList ihs' (consList fs (consList ms (cons M ρp)))) body = C) →
      interp2 V (consList ihs (consList fs (consList ms (cons M ρp))))
          (ihPisAV nF o b tls Eiss is l body)
        = ihSpL ℓ C (is.map fun i =>
            piTele ℓ (teleOfFields (consList (fs.take i) ρp) ((tls.getD i []).map (·.2.2)))
              (fun as => SetTheory.app
                (((Eiss.getD i []).map (interp2 V (consList as (consList (fs.take i) ρp)))).foldl
                  SetTheory.app M)
                (as.foldl SetTheory.app (fs.getD i pt))) [])
  | [], l, ihs, body, hihs, _, _, hbody => by
    simp only [ihPisAV, List.map_nil, ihSpL]
    exact hbody ihs (by simp [hihs])
  | i :: is, l, ihs, body, hihs, hlt, hbits, hbody => by
    simp only [ihPisAV, List.map_cons, ihSpL, interp2_pi]
    rw [piR_congr_bit (v := b) (v' := ℓ) hbz.symm,
      interp_ihDomAV hms hfs hihs (hlt i List.mem_cons_self) (hbits i List.mem_cons_self)]
    apply piR_congr
    intro x _
    rw [consList_snoc']
    refine interp_ihPisAV hbz hms hfs is (l + 1) (ihs ++ [x]) body (by simp [hihs])
      (fun i' hi' => hlt i' (List.mem_cons_of_mem _ hi'))
      (fun i' hi' => hbits i' (List.mem_cons_of_mem _ hi')) ?_
    intro ihs' hl
    exact hbody ihs' (by rw [hl, List.length_cons]; omega)

end Lech.SetP
