import Lech.SetP.DirectFix.FixRecPreP
import Lech.SetP.DirectFix.FixIntroP

/-!
# The rule right-hand side's gradedness: the kit (task #188)

The sum route certifies a rule's right-hand side by the kernel's own
inference run at the pre-recursor environment; a recursive rule
mentions the recursor, so its gradedness is proved semantically from
the model instead (`FixRuleOkP.lean`).  This module holds the kit: the
minor space's application chain, the ih-moved index expressions'
grading and validity, domain walks over prefixes, appends and lifted
fields, and the validity walk over binder data.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The minor space's application chain -/

/-- A minor-space member applied along a fitting spine is a graded
application chain. -/
theorem minorSpI_appChainOk {ℓ : Nat} {c : List V → V}
    (hc0 : ℓ = 0 → ∀ acc, c acc ∈ˢ (univZero : V)) :
    ∀ {Fs : List AVExpr} {ρf : Nat → V} {acc : List V} {m : V} {as : List V},
      m ∈ˢ minorSpI ℓ c Fs ρf acc → SpineFit ρf Fs as → AppChainOk m as
  | [], _, _, _, [], _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | [], _, _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρf, acc, m, a :: as, hm, hsp => by
    have hB0 : ℓ = 0 → ∀ x, x ∈ˢ interp2 V ρf F →
        minorSpI ℓ c Fs (cons x ρf) (acc ++ [x]) ∈ˢ (univZero : V) :=
      fun h0 x _ => minorSpI_zero_univZero h0 (hc0 h0) Fs (cons x ρf) (acc ++ [x])
    have happ : SetTheory.app m a ∈ˢ minorSpI ℓ c Fs (cons a ρf) (acc ++ [a]) :=
      app_mem_piR hm hsp.1 hB0
    intro l hl
    cases l with
    | zero =>
      exact ⟨ℓ, interp2 V ρf F, fun x => minorSpI ℓ c Fs (cons x ρf) (acc ++ [x]), hm,
        by simpa using hsp.1, hB0⟩
    | succ l =>
      obtain ⟨v, A, B, h1, h2, h3⟩ := minorSpI_appChainOk hc0 (Fs := Fs) (as := as) happ hsp.2 l
        (by simpa using hl)
      refine ⟨v, A, B, ?_, ?_, h3⟩
      · simpa only [List.take_succ_cons, List.foldl_cons] using h1
      · simpa only [List.getD_cons_succ] using h2


/-! ## The ih-moved telescopes (task #202) -/

theorem AnnotOk2_ihIdxAtM {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) (as : List V) (E : AVExpr) :
    AnnotOk2 V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l as.length E) ↔
      AnnotOk2 V (consList as (consList (fs.take i) ρp)) E := by
  unfold ihIdxAtM
  rw [AnnotOk2_liftN, show nF + l + as.length = as.length + (fs.length + ihs.length) from by omega,
    shiftE_consList_len', shiftE_fieldFrame hms, AnnotOk2_liftN, shiftE_consList_len,
    ← consList_append]
  have hsplit : fs ++ ihs = fs.take i ++ (fs.drop i ++ ihs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, consList_append, show nF - i + l = (fs.drop i ++ ihs).length from by
    rw [List.length_append, List.length_drop]; omega, shiftE_consList]

theorem AnnotValidV_ihIdxAtM {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) (as : List V) (E : AVExpr) :
    AnnotValidV V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l as.length E) ↔
      AnnotValidV V (consList as (consList (fs.take i) ρp)) E := by
  unfold ihIdxAtM
  rw [AnnotValidV_liftN, show nF + l + as.length = as.length + (fs.length + ihs.length) from by omega,
    shiftE_consList_len', shiftE_fieldFrame hms, AnnotValidV_liftN, shiftE_consList_len,
    ← consList_append]
  have hsplit : fs ++ ihs = fs.take i ++ (fs.drop i ++ ihs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, consList_append, show nF - i + l = (fs.drop i ++ ihs).length from by
    rw [List.length_append, List.length_drop]; omega, shiftE_consList]

/-- A spine fits the moved telescope at the ih frame iff it fits the
telescope at the field's own frame. -/
theorem spineFit_ihTeleAtGo {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) :
    ∀ (tl : List (Nat × Nat × AVExpr)) (as bs : List V),
      SpineFit (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
          ((ihTeleAtGo nF o i l as.length tl).map (·.2.2)) bs ↔
        SpineFit (consList as (consList (fs.take i) ρp)) (tl.map (·.2.2)) bs
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => by simp [ihTeleAtGo, SpineFit]
  | d :: tl, as, b :: bs => by
    show b ∈ˢ interp2 V (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        (ihIdxAtM nF o i l as.length d.2.2) ∧ SpineFit _ _ bs ↔
      b ∈ˢ interp2 V (consList as (consList (fs.take i) ρp)) d.2.2 ∧ SpineFit _ _ bs
    rw [interp_ihIdxAtM hms hfs hihs hi, consList_snoc', consList_snoc']
    have := spineFit_ihTeleAtGo (M := M) (ρp := ρp) hms hfs hihs hi tl (as ++ [b]) bs
    rw [length_snoc'] at this
    rw [this]

/-- The telescope's grading moved to the ih frame. -/
theorem fieldsOkB_ihTeleAtGo {w nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) :
    ∀ (tl : List (Nat × Nat × AVExpr)) (as : List V),
      FieldsOkB w (consList as (consList (fs.take i) ρp)) (tl.map (·.2.2)) →
      FieldsOkB w (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        ((ihTeleAtGo nF o i l as.length tl).map (·.2.2))
  | [], _, _ => trivial
  | d :: tl, as, hF => by
    show FieldsOkB w _ (ihIdxAtM nF o i l as.length d.2.2 ::
      (ihTeleAtGo nF o i l (as.length + 1) tl).map (·.2.2))
    rw [List.map_cons] at hF
    obtain ⟨hok, hbnd, hrest⟩ := hF
    refine ⟨(AnnotOk2_ihIdxAtM hms hfs hihs hi as _).mpr hok,
      fun hw => by rw [interp_ihIdxAtM hms hfs hihs hi]; exact hbnd hw, fun a ha => ?_⟩
    rw [interp_ihIdxAtM hms hfs hihs hi] at ha
    rw [consList_snoc']
    have := fieldsOkB_ihTeleAtGo (M := M) (ρp := ρp) hms hfs hihs hi tl (as ++ [a])
      (by rw [← consList_snoc']; exact hrest a ha)
    rw [length_snoc'] at this
    exact this

/-- The telescope's validity moved to the ih frame. -/
theorem fieldsValid_ihTeleAtGo {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) :
    ∀ (tl : List (Nat × Nat × AVExpr)) (as : List V),
      FieldsValid (consList as (consList (fs.take i) ρp)) (tl.map (·.2.2)) →
      FieldsValid (consList as (consList ihs (consList fs (consList ms (cons M ρp)))))
        ((ihTeleAtGo nF o i l as.length tl).map (·.2.2))
  | [], _, _ => trivial
  | d :: tl, as, hF => by
    show FieldsValid _ (ihIdxAtM nF o i l as.length d.2.2 ::
      (ihTeleAtGo nF o i l (as.length + 1) tl).map (·.2.2))
    rw [List.map_cons] at hF
    obtain ⟨hv, hrest⟩ := hF
    refine ⟨(AnnotValidV_ihIdxAtM hms hfs hihs hi as _).mpr hv, fun a ha => ?_⟩
    rw [interp_ihIdxAtM hms hfs hihs hi] at ha
    rw [consList_snoc']
    have := fieldsValid_ihTeleAtGo (M := M) (ρp := ρp) hms hfs hihs hi tl (as ++ [a])
      (by rw [← consList_snoc']; exact hrest a ha)
    rw [length_snoc'] at this
    exact this

/-- A graded telescope walks. -/
theorem domsWalk_of_fieldsOkB {w : Nat} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      FieldsOkB w ρ (ds.map (·.2.2)) → DomsWalk ρ ds
  | [], _, _ => trivial
  | _ :: ds, ρ, h => by
    rw [List.map_cons] at h
    exact ⟨h.1, fun a ha => domsWalk_of_fieldsOkB (h.2.2 a ha)⟩

/-! ## λ-towers with the binders' own bits -/

/-- **A λ-tower with the telescope's own bits inhabits its Π-tower's
reading** (`mkLamsC_mem` with per-binder bits). -/
theorem mkLamsAV_bits_mem {m : Nat} {b T : AVExpr} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → UnderTowerOk m ρ b T ds →
      interp2 V ρ (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b) ∈ˢ interp2 V ρ (mkPisAV ds T)
  | [], _, _, h => h.2.1
  | d :: ds, ρ, hz, h => by
    show (lamR d.2.1 (interp2 V ρ d.2.2)
        fun a => interp2 V (cons a ρ) (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b))
      ∈ˢ piR d.2.1 (interp2 V ρ d.2.2) fun a => interp2 V (cons a ρ) (mkPisAV ds T)
    exact lamR_mem_zero_agree Iff.rfl
      fun a ha => mkLamsAV_bits_mem (fun d' hd' => hz d' (.tail _ hd')) (h.2 a ha)

/-- **A λ-tower with the telescope's own bits is graded.** -/
theorem mkLamsAV_bits_ok2 {m : Nat} {b T : AVExpr} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → UnderTowerOk m ρ b T ds →
      AnnotOk2 V ρ (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b)
  | [], _, _, h => h.1
  | d :: ds, ρ, hz, h => by
    show AnnotOk2 V ρ (.lam d.2.1 d.2.2 (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b))
    rw [AnnotOk2_lam]
    refine ⟨h.1, fun a ha => mkLamsAV_bits_ok2 (fun d' hd' => hz d' (.tail _ hd')) (h.2 a ha),
      ⟨fun a => interp2 V (cons a ρ) (mkPisAV ds T),
       fun a ha => mkLamsAV_bits_mem (fun d' hd' => hz d' (.tail _ hd')) (h.2 a ha),
       fun h0 a ha => underTowerOk_res_univZero ((hz d (.head _)).mpr h0)
         (fun d' hd' => hz d' (.tail _ hd')) (h.2 a ha)⟩⟩

/-- **A λ-tower with the telescope's own bits is bit-valid.** -/
theorem mkLamsAV_bits_validV {b : AVExpr} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      UnderTowerValid ρ b ds → AnnotValidV V ρ (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b)
  | [], _, h => h
  | d :: ds, ρ, h => by
    show AnnotValidV V ρ (.lam d.2.1 d.2.2 (mkLamsAV (ds.map fun d => (d.2.1, d.2.2)) b))
    rw [AnnotValidV_lam]
    exact ⟨h.1, fun a ha => mkLamsAV_bits_validV (h.2 a ha)⟩

/-! ## The slot's value along a telescope spine -/

/-- A family's applications are bounded by its universe (junk off the
index set). -/
theorem famApp_mem_univ {w : Nat} {I X : V} (hX : X ∈ˢ lfpFamSpace V w I) (t : V) :
    SetTheory.app X t ∈ˢ (univ w : V) := by
  by_cases ht : t ∈ˢ I
  · exact app_mem_piR_pos (Nat.succ_ne_zero w) hX ht
  · rw [(mem_piR_pos (Nat.succ_ne_zero w) hX).2.2.1 t ht]
    exact empty_mem_univ w

/-- **A field in a slot's value, applied along a fitting telescope
spine, lies in the family at the index values** (task #202). -/
theorem slotSet_fold_mem {w u : Nat} {ρ : Nat → V} {tl : List (Nat × Nat × AVExpr)}
    {Eis : List AVExpr} {X : V} (hX : ∀ t, SetTheory.app X t ∈ˢ (univ w : V)) {f : V}
    (hf : f ∈ˢ slotSet w u ρ tl Eis X) {bs : List V} (hsp : SpineFit ρ (tl.map (·.2.2)) bs) :
    bs.foldl SetTheory.app f
      ∈ˢ SetTheory.app X (tupW u (Eis.map (interp2 V (consList bs ρ)))) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have hpt : f = pt := eq_pt_of_mem_slotSet_zero (fun t => by rw [← univ_zero]; exact hX t) hf
    unfold slotSet at hf
    obtain ⟨y, hy⟩ := mem_piTele_zero hf bs (fitsS_teleOfFields.mpr hsp)
    rw [List.nil_append] at hy
    have hz : SetTheory.app X (tupW u (Eis.map (interp2 V (consList bs ρ)))) ∈ˢ (univZero : V) := by
      rw [← univ_zero]; exact hX _
    rw [hpt, foldl_app_pt_sum, ← eq_pt_of_mem_univZero hz hy]
    exact hy
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    unfold slotSet at hf
    have := piTele_fold hw' hf (fitsS_teleOfFields.mpr hsp)
    rwa [List.nil_append] at this

/-- **A field in a slot's value has a graded application chain** along
a fitting telescope spine. -/
theorem slotSet_chainOk {w u : Nat} {ρ : Nat → V} {tl : List (Nat × Nat × AVExpr)}
    {Eis : List AVExpr} {X : V} (hX : ∀ t, SetTheory.app X t ∈ˢ (univ w : V)) {f : V}
    (hf : f ∈ˢ slotSet w u ρ tl Eis X) {bs : List V} (hsp : SpineFit ρ (tl.map (·.2.2)) bs) :
    AppChainOk f bs := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · -- the field is the point: every prefix application is the point, in
    -- a `Prop`-regime product over the next domain with inhabited fibres
    have hpt : f = pt := eq_pt_of_mem_slotSet_zero (fun t => by rw [← univ_zero]; exact hX t) hf
    subst hpt
    intro l hl
    have hlen : bs.length = tl.length := by rw [hsp.length_eq, List.length_map]
    refine ⟨0, interp2 V (consList (bs.take l) ρ) ((tl.map (·.2.2)).getD l default),
      fun _ => truthVal True, ?_, ?_, fun _ _ _ => truthVal_mem_univZero True⟩
    · rw [foldl_app_pt_sum, piR_zero]
      exact mem_truthVal.mpr ⟨fun _ _ => ⟨pt, mem_truthVal.mpr ⟨trivial, rfl⟩⟩, rfl⟩
    · exact FixKI.spineFit_getD_mem' hsp (by rw [List.length_map]; omega)
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    unfold slotSet at hf
    exact piTele_chainOk hw' hf (fitsS_teleOfFields.mpr hsp)

/-! ## The ih-moved index expressions -/

/-- The ih-moved index expression is graded exactly when the expression
is at the field's own frame. -/
theorem AnnotOk2_ihIdxAt {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) (E : AVExpr) :
    AnnotOk2 V (consList ihs (consList fs (consList ms (cons M ρp)))) (ihIdxAt nF o i l E) ↔
      AnnotOk2 V (consList (fs.take i) ρp) E := by
  unfold ihIdxAt
  rw [AnnotOk2_liftN, show nF + l = fs.length + ihs.length from by omega, shiftE_fieldFrame hms,
    AnnotOk2_liftN, ← consList_append]
  have hsplit : fs ++ ihs = fs.take i ++ (fs.drop i ++ ihs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, consList_append, show nF - i + l = (fs.drop i ++ ihs).length from by
    rw [List.length_append, List.length_drop]; omega, shiftE_consList]

/-- The ih-moved index expression is valid exactly when the expression
is at the field's own frame. -/
theorem AnnotValidV_ihIdxAt {nF o i l : Nat} {ρp : Nat → V} {M : V} {ms : List V}
    (hms : ms.length + 1 = o) {fs ihs : List V} (hfs : fs.length = nF) (hihs : ihs.length = l)
    (hi : i ≤ nF) (E : AVExpr) :
    AnnotValidV V (consList ihs (consList fs (consList ms (cons M ρp)))) (ihIdxAt nF o i l E) ↔
      AnnotValidV V (consList (fs.take i) ρp) E := by
  unfold ihIdxAt
  rw [AnnotValidV_liftN, show nF + l = fs.length + ihs.length from by omega, shiftE_fieldFrame hms,
    AnnotValidV_liftN, ← consList_append]
  have hsplit : fs ++ ihs = fs.take i ++ (fs.drop i ++ ihs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, consList_append, show nF - i + l = (fs.drop i ++ ihs).length from by
    rw [List.length_append, List.length_drop]; omega, shiftE_consList]

/-! ## Domain walks -/

/-- A walk over a prefix. -/
theorem domsWalk_take :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V} (k : Nat),
      DomsWalk ρ ds → DomsWalk ρ (ds.take k)
  | [], _, _, _ => by simp [DomsWalk]
  | _ :: _, _, 0, _ => trivial
  | d :: ds, ρ, k + 1, h => ⟨h.1, fun a ha => domsWalk_take k (h.2 a ha)⟩

/-- A walk over an append: the prefix's walk and the suffix's at every
fitting spine of the prefix. -/
theorem domsWalk_append :
    ∀ {xs ys : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      DomsWalk ρ xs →
      (∀ as : List V, SpineFit ρ (xs.map (·.2.2)) as → DomsWalk (consList as ρ) ys) →
      DomsWalk ρ (xs ++ ys)
  | [], ys, ρ, _, hys => by simpa using hys [] trivial
  | x :: xs, ys, ρ, hx, hys => by
    refine ⟨hx.1, fun a ha => domsWalk_append (hx.2 a ha) fun as hsp => ?_⟩
    have := hys (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- A walk is insensitive to the bits. -/
theorem domsWalk_rebit (b : Nat) :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V}, DomsWalk ρ ds → DomsWalk ρ (rebit b ds)
  | [], _, _ => trivial
  | _ :: ds, _, h => ⟨h.1, fun a ha => domsWalk_rebit b (ds := ds) (h.2 a ha)⟩

/-- Lifted fields walk at a frame shifting to a frame where they are
graded. -/
theorem domsWalk_liftDoms {w n : Nat} :
    ∀ (ds : List (Nat × Nat × AVExpr)) (k : Nat) (σ : Nat → V),
      FieldsOkB w (shiftE n k σ) (ds.map (·.2.2)) → DomsWalk σ (liftDoms n k ds)
  | [], _, _, _ => trivial
  | d :: ds, k, σ, h => by
    refine ⟨?_, fun a ha => ?_⟩
    · show AnnotOk2 V σ (d.2.2.liftN n k)
      rw [AnnotOk2_liftN]; exact h.1
    · have ha' : a ∈ˢ interp2 V (shiftE n k σ) d.2.2 := by
        rwa [show interp2 V σ (d.2.2.liftN n k) = interp2 V (shiftE n k σ) d.2.2 from
          interp2_liftN V n d.2.2 k σ] at ha
      refine domsWalk_liftDoms (w := w) ds (k + 1) (cons a σ) ?_
      rw [shiftE_succ_cons']
      exact h.2.2 a ha'

/-! ## Validity walks -/

/-- A tower is valid under binder data from the validity of every
domain at its prefix's fitting spines and of the body at the leaves. -/
theorem underTowerValid_of :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V} {b : AVExpr},
      (∀ k d, ds[k]? = some d → ∀ as : List V, SpineFit ρ ((ds.take k).map (·.2.2)) as →
        AnnotValidV V (consList as ρ) d.2.2) →
      (∀ as : List V, SpineFit ρ (ds.map (·.2.2)) as → AnnotValidV V (consList as ρ) b) →
      UnderTowerValid ρ b ds
  | [], ρ, b, _, hb => by
    have := hb [] trivial
    rwa [consList_nil] at this
  | d :: ds, ρ, b, hd, hb => by
    refine ⟨by have := hd 0 d rfl [] trivial; rwa [consList_nil] at this,
      fun a ha => underTowerValid_of ?_ ?_⟩
    · intro k d' hk as hsp
      have := hd (k + 1) d' (by simpa using hk) (a :: as) ⟨ha, hsp⟩
      rwa [consList_cons] at this
    · intro as hsp
      have := hb (a :: as) ⟨ha, hsp⟩
      rwa [consList_cons] at this

end Lech.SetP
