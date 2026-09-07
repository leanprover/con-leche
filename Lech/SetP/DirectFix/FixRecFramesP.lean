import Lech.SetP.DirectFix.FixRecReadDefsP
import Lech.SetP.DirectFix.FixRealChainsP
import Lech.SetP.DirectSum.SumRecFramesP
import Lech.Semantics.Tower.FixSquashI

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

/-- The ih domain's body under `as` telescope values: the motive at the
field's index values (under those values) at the field applied to
them. -/
theorem interp_ihDomBody {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i < nF) (as : List V) (Eis : List AVExpr) :
    interp2 V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        (AVExpr.mkAppN (.bvar (nF + o - 1 + l + as.length))
          (Eis.map (ihIdxAtM nF o i l as.length) ++
            [AVExpr.mkAppN (.bvar (nF - 1 - i + l + as.length)) (teleVarsAV as.length)]))
      = SetTheory.app
          ((Eis.map (interp2 V (consList as (consList (fs.take i) ρp)))).foldl SetTheory.app M)
          (as.foldl SetTheory.app (fs.getD i pt)) := by
  rw [AVExpr.mkAppN_append_one, interp2_app, interp2_mkAppN,
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
    rw [List.nil_append, ← hlen]
    exact interp_ihDomBody hms hfs hihs hi as Eis

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
