module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Denote.Depth
import ConLeche.Verify.Denote.Inst
import ConLeche.Verify.InstSpine
import ConLeche.Verify.Leaves
import ConLeche.Verify.Shift

public section

/-!
# The soundness of the wider unit-like η and of the partial-constructor η (task #515)

The rules of official's `is_unit_like` (lean4#15372) and of the η-expansion of a
partially applied constructor (lean4#15373), at the conditional motive.

* **Two members of a function space are equal where all their applications
  are** (`piV_ext`): a member is the abstraction of its applications
  (`lamV_eta`).  The ∀ arm of `UnitLike` and the expansion step of
  `DefEqExpand` both open the ∀ at a fresh variable and read the claim at
  every value of it.
* **An instance of an η family** is the constructor at the parameters and
  its own projections (its table's η law, at every field count), and that
  spine fits the constructor's telescope (the coherence law).  Two members fit it at the
  same parameters, so their projections fit the field telescope the checker
  walks (`unitFieldTele`, the parameters substituted; `unitTele_fit`), whose
  fields are propositions (every proof is the point) or unit-like: the
  projections coincide field by field, and so do the members (at a fieldless
  family there is nothing to compare: both members are the constructor at the
  parameters).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

/-- **Two members of a function space whose fibres are types are equal where
all their applications are.** -/
theorem piV_ext {A f g : V} {B : V → V} (hf : f ∈ˢ piV A B) (hg : g ∈ˢ piV A B)
    (hB : ∀ x, x ∈ˢ A → IsTy (B x)) (h : ∀ x, x ∈ˢ A → app f x = app g x) : f = g := by
  rw [← lamV_eta hf hB, ← lamV_eta hg hB]
  exact lamV_congr h

/-! ## Opening a ∀ at a fresh variable -/

/-- The frame of a side applied to the opened variable. -/
theorem Frame.app_fvar {d : Nat} {a dom : Expr} (ha : Frame d a) (hdom : Frame d dom) :
    Frame (d + 1) (.app a (.fvar d dom)) := by
  obtain ⟨hwa, hba, hLa⟩ := ha
  obtain ⟨hwd, hbd, hLd⟩ := hdom
  refine ⟨?_, by simp [Expr.looseBVarsBounded, hba], fun l hl => ?_⟩
  · simp only [Expr.WScoped]
    exact ⟨Expr.WScoped.mono (by omega) hwa, by omega, hwd⟩
  · rw [ConLeche.Expr.fvarLeaves] at hl
    rcases List.mem_append.mp hl with h2 | h2
    · exact hLa l h2
    · rw [ConLeche.Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact hbd
      · exact hLd l h3

/-- **The opened application**: a side `a` applied to the fresh variable of a
graded domain `dom` — its context, reading and leaves at the extended valuation,
its value the application of `a`'s, graded where `a` is a member of the
function space. -/
theorem open_app {d : Nat} {Δa : List Term} {a dom : Expr} {aa doma : Term}
    {ρ : Nat → V} (hfa : Frame d a) (hCa : CtxOkS m φ d Δa a) (hCd : CtxOkS m φ d Δa dom)
    (hda : denote m.acval env φ d a = some aa) (hdd : denote m.acval env φ d dom = some doma)
    (hLa : LeavesGr m φ d a ρ) (hLd : LeavesGr m φ d dom ρ) (hokd : WellDenotedTy V ρ doma) :
    CtxOkS m φ (d + 1) (doma :: Δa) (.app a (.fvar d dom)) ∧
      denote m.acval env φ (d + 1) (.app a (.fvar d dom)) = some (.app aa.lift (.bvar 0)) ∧
      (∀ z : V, LeavesGr m φ (d + 1) (.app a (.fvar d dom)) (cons z ρ)) ∧
      (∀ z : V, interp V (cons z ρ) (.app aa.lift (.bvar 0)) = SetTheory.app (interp V ρ aa) z) ∧
      (∀ (B : V → V) (z : V), WellDenoted V ρ aa → interp V ρ aa ∈ˢ piV (interp V ρ doma) B →
        z ∈ˢ interp V ρ doma → WellDenoted V (cons z ρ) (.app aa.lift (.bvar 0))) := by
  have hdaUp : denote m.acval env φ (d + 1) a = some aa.lift := by
    rw [denote_weaken_top m.acval_closed hfa.1, hda]; rfl
  have hCfvar : CtxOkS m φ (d + 1) (doma :: Δa) (.fvar d dom) := by
    have := CtxOkS.openS (body := Expr.bvar 0) hCd
      (CtxOkS.of_fvarLeaves_nil hCa.length (by simp [Expr.fvarLeaves])) hdd
    simpa [Expr.instantiate1] using this
  have hLfvar : ∀ z : V, LeavesGr m φ (d + 1) (.fvar d dom) (cons z ρ) := by
    intro z
    have := LeavesGr.open (body := Expr.bvar 0) (x := z) hCd
      (CtxOkS.of_fvarLeaves_nil hCa.length (by simp [Expr.fvarLeaves]))
      hLd (LeavesGr.of_fvarLeaves_nil (by simp [Expr.fvarLeaves])) hdd hokd
    simpa [Expr.instantiate1] using this
  refine ⟨CtxOkS.app (CtxOkS.weakenTop hCa) hCfvar, ?_,
    fun z => LeavesGr.app (LeavesGr.weakenTop (ρ := cons z ρ) hCa hLa) (hLfvar z),
    fun z => by rw [interp_app, interp_lift_cons, interp_bvar]; rfl,
    fun B z hok hmem hz => ?_⟩
  · rw [denote, hdaUp, denote_fvar]
    simp
  · have hok0 : WellDenoted V (cons z ρ) aa.lift :=
      (WellDenoted_liftN V 1 aa 0 (cons z ρ)).mpr (by rw [shiftE_zero]; exact hok)
    rw [WellDenoted_app]
    refine ⟨hok0, by simp, _, interp V ρ doma, B, ?_, hz, propN_eq_zero.mp,
      fun _ => hokd.2⟩
    rw [interp_lift_cons]; exact hmem

/-! ## The η-expansion (`DefEqExpand`) -/

/-- The full applications, compared: two members of one type, both the
point or neither (`IsTy.eq_of_ne_pt`). -/
theorem DefEqExpand.done_sound {d : Nat} {a b T : Expr} (h : DefEqSem m φ d a b) :
    DefEqExpandSem m φ d a b T := by
  intro hfa hfb _ Δa aa ba Ta hCa hCb _ hda hdb _ ρ hρ hLa hLb _ hwa hwb hokT hma hmb
  exact IsTy.eq_of_ne_pt hokT.2 hma hmb fun hna hnb =>
    h hfa hfb hCa hCb hda hdb ρ hρ hLa hLb hwa hwb hna hnb

/-- One binder: both sides applied to the fresh variable of the ∀'s domain
are members of its fibre, equal at every value of it (`piV_ext`). -/
theorem DefEqExpand.step_sound {d : Nat} {a b dom body : Expr}
    (ih : DefEqExpandSem m φ (d + 1) (.app a (.fvar d dom)) (.app b (.fvar d dom))
      (body.instantiate1 (.fvar d dom))) :
    DefEqExpandSem m φ d a b (.forallE dom body) := by
  intro hfa hfb hfT Δa aa ba Ta hCa hCb hCT hda hdb hdT ρ hρ hLa hLb hLT hwa hwb hokT hma hmb
  obtain ⟨doma, bda, hdoma, hbda, rfl⟩ := denote_forallE_inv hdT
  have hpi := hokT.1
  rw [WellDenoted_pi] at hpi
  obtain ⟨hwd, htyd, hwB, htyB⟩ := hpi
  have hokd : WellDenotedTy V ρ doma := ⟨hwd, htyd⟩
  rw [interp_pi] at hma hmb
  have hfd : Frame d dom := hfT.forallE_ty
  have hCd : CtxOkS m φ d Δa dom := hCT.forallE_ty
  have hLd : LeavesGr m φ d dom ρ := hLT.forallE_ty
  obtain ⟨hCA, hdA, hLA, hiA, hwA⟩ := open_app hfa hCa hCd hda hdoma hLa hLd hokd
  obtain ⟨hCB, hdB, hLB, hiB, hwB'⟩ := open_app hfb hCb hCd hdb hdoma hLb hLd hokd
  refine piV_ext hma hmb htyB fun z hz => ?_
  have h := ih (Frame.app_fvar hfa hfd) (Frame.app_fvar hfb hfd) (hfT.forallE_open hfd)
    hCA hCB (CtxOkS.openS hCd hCT.forallE_body hdoma) hdA hdB hbda (cons z ρ)
    (Sat_cons V hρ hz) (hLA z) (hLB z)
    (LeavesGr.open hCd hCT.forallE_body hLd hLT.forallE_body hdoma hokd)
    (hwA _ z hwa hma hz) (hwB' _ z hwb hmb hz) ⟨hwB z hz, htyB z hz⟩
    (by rw [hiA]; exact app_mem_piV hma hz) (by rw [hiB]; exact app_mem_piV hmb hz)
  rwa [hiA, hiB] at h

/-- **η of a partially applied constructor**: two neutral sides that are not
the point are members of their io-inferred types, which the comparison makes
one; the expansion then equates them. -/
theorem DefEq.etaExpand_sound {d : Nat} {a ta b tb : Expr}
    (hna : a.ioNeutral = true) (hnb : b.ioNeutral = true)
    (hta : InferSemIO m φ d a ta) (htb : InferSemIO m φ d b tb)
    (hd : DefEqSem m φ d tb ta) (hex : DefEqExpandSem m φ d a b ta) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb ρ hρ hLa hLb hwa hwb hna' hnb'
  obtain ⟨hfta, hsuba, taa, htaa, hXA⟩ := hta hfa hCa hda
  obtain ⟨hftb, hsubb, tba, htba, hXB⟩ := htb hfb hCb hdb
  have hmA : WellDenotedTy V ρ taa ∧ interp V ρ aa ∈ˢ interp V ρ taa := by
    rcases (hXA ρ hρ hLa hwa).2 hna with h | h
    · exact absurd h hna'
    · exact h.of_reading htaa
  have hmB : WellDenotedTy V ρ tba ∧ interp V ρ ba ∈ˢ interp V ρ tba := by
    rcases (hXB ρ hρ hLb hwb).2 hnb with h | h
    · exact absurd h hnb'
    · exact h.of_reading htba
  have hCta : CtxOkS m φ d Δa ta := hCa.of_subset hsuba
  have hCtb : CtxOkS m φ d Δa tb := hCb.of_subset hsubb
  have heq : interp V ρ tba = interp V ρ taa :=
    hd hftb hfta hCtb hCta htba htaa ρ hρ (hLb.of_subset hsubb) (hLa.of_subset hsuba)
      hmB.1.1 hmA.1.1 hmB.1.2.ne_pt hmA.1.2.ne_pt
  exact hex hfa hfb hfta hCa hCb hCta hda hdb htaa ρ hρ hLa hLb (hLa.of_subset hsuba)
    hwa hwb hmA.1 hmA.2 (heq ▸ hmB.2)

/-! ## A unit-like ∀ -/

/-- **A ∀ whose opened codomain is unit-like**: two members agree at every
value of the variable. -/
theorem UnitLike.pi_sound {d : Nat} {T dom body : Expr}
    (hr : RedSem m φ d T (.forallE dom body))
    (ih : UnitLikeSem m φ (d + 1) (body.instantiate1 (.fvar d dom))) :
    UnitLikeSem m φ d T := by
  intro hfT Δa Ta hCT hdT ρ hρ hLT hokT x y hx hy
  obtain ⟨hfW, hsubW, wa, hwa, hY⟩ := hr hfT hCT hdT
  obtain ⟨hokW, heqW⟩ := hY ρ hρ hLT hokT.1 hokT.2.ne_pt
  have hCW : CtxOkS m φ d Δa (.forallE dom body) := hCT.of_subset hsubW
  have hLW : LeavesGr m φ d (.forallE dom body) ρ := hLT.of_subset hsubW
  obtain ⟨doma, bda, hdoma, hbda, rfl⟩ := denote_forallE_inv hwa
  have hpi := hokW
  rw [WellDenoted_pi] at hpi
  obtain ⟨hwd, htyd, hwB, htyB⟩ := hpi
  have hokd : WellDenotedTy V ρ doma := ⟨hwd, htyd⟩
  rw [heqW, interp_pi] at hx hy
  have hfd : Frame d dom := hfW.forallE_ty
  have hCd : CtxOkS m φ d Δa dom := hCW.forallE_ty
  have hLd : LeavesGr m φ d dom ρ := hLW.forallE_ty
  refine piV_ext hx hy htyB fun z hz => ?_
  exact ih (hfW.forallE_open hfd) (CtxOkS.openS hCd hCW.forallE_body hdoma) hbda (cons z ρ)
    (Sat_cons V hρ hz) (LeavesGr.open hCd hCW.forallE_body hLd hLW.forallE_body hdoma hokd)
    ⟨hwB z hz, htyB z hz⟩ _ _ (app_mem_piV hx hz) (app_mem_piV hy hz)

/-! ## The field telescope -/

/-- No field: the empty spines. -/
theorem UnitFields.nil_sound {d : Nat} {tele : Expr} : UnitFieldsSem m φ d tele 0 := by
  intro _ _ _ _ _ _ _ _ _ xs ys _ _ hx hy _ _
  rw [List.length_eq_zero_iff.mp hx, List.length_eq_zero_iff.mp hy]

/-- **A field and the rest**: the field's values are equal by `hfield` (a
proposition's members are the point; a unit-like type's are equal), and the
rest fits the body opened at that value. -/
theorem UnitFields.cons_sound {d n : Nat} {dom body : Expr}
    (hfield : ∀ {Δa : List Term} {doma : Term}, Frame d dom → CtxOkS m φ d Δa dom →
      denote m.acval env φ d dom = some doma →
      ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d dom ρ → WellDenotedTy V ρ doma →
        ∀ x y : V, x ∈ˢ interp V ρ doma → y ∈ˢ interp V ρ doma → x = y)
    (ih : UnitFieldsSem m φ (d + 1) (body.instantiate1 (.fvar d dom)) n) :
    UnitFieldsSem m φ d (.forallE dom body) (n + 1) := by
  intro hfT Δa telea hCT hdT ρ hρ hLT hokT xs ys rx ry hlx hly hfx hfy
  obtain ⟨doma, bda, hdoma, hbda, rfl⟩ := denote_forallE_inv hdT
  have hpi := hokT
  rw [WellDenoted_pi] at hpi
  obtain ⟨hwd, htyd, hwB, -⟩ := hpi
  have hokd : WellDenotedTy V ρ doma := ⟨hwd, htyd⟩
  have hfd : Frame d dom := hfT.forallE_ty
  have hCd : CtxOkS m φ d Δa dom := hCT.forallE_ty
  have hLd : LeavesGr m φ d dom ρ := hLT.forallE_ty
  cases hfx with
  | nil => simp at hlx
  | @cons _ _ _ x xs' _ hx hfx' =>
    cases hfy with
    | nil => simp at hly
    | @cons _ _ _ y ys' _ hy hfy' =>
      obtain rfl : x = y := hfield hfd hCd hdoma ρ hρ hLd hokd x y hx hy
      have hrest := ih (hfT.forallE_open hfd) (CtxOkS.openS hCd hCT.forallE_body hdoma) hbda
        (cons x ρ) (Sat_cons V hρ hx)
        (LeavesGr.open hCd hCT.forallE_body hLd hLT.forallE_body hdoma hokd)
        (hwB x hx) xs' ys' _ _ (by simpa using hlx) (by simpa using hly) hfx' hfy'
      rw [hrest]

/-- A proposition's field: its io claim is the point. -/
theorem UnitFields.prop_sound {d n : Nat} {dom body : Expr} (hpt : PropPt m φ d dom)
    (ih : UnitFieldsSem m φ (d + 1) (body.instantiate1 (.fvar d dom)) n) :
    UnitFieldsSem m φ d (.forallE dom body) (n + 1) :=
  UnitFields.cons_sound (fun hfd hCd hdoma ρ hρ hLd hokd x y hx hy => by
    rw [hpt hfd hCd hdoma ρ x hρ hLd (Or.inr (Or.inl ⟨_, hdoma, hokd, hx⟩)),
      hpt hfd hCd hdoma ρ y hρ hLd (Or.inr (Or.inl ⟨_, hdoma, hokd, hy⟩))]) ih

/-- A unit-like field. -/
theorem UnitFields.unit_sound {d n : Nat} {dom body : Expr} (hu : UnitLikeSem m φ d dom)
    (ih : UnitFieldsSem m φ (d + 1) (body.instantiate1 (.fvar d dom)) n) :
    UnitFieldsSem m φ d (.forallE dom body) (n + 1) :=
  UnitFields.cons_sound (fun hfd hCd hdoma ρ hρ hLd hokd x y hx hy =>
    hu hfd hCd hdoma ρ hρ hLd hokd x y hx hy) ih

/-! ## The field telescope of an instance, syntactically -/

/-- Instantiation commutes with a peel, at the cursor moved past the peeled
binders. -/
theorem peelPis_instantiate1 {a : Expr} :
    ∀ (k : Nat) {B F : Expr} (c : Nat), Expr.peelPis k B = some F →
      Expr.peelPis k (B.instantiate1 a c) = some (F.instantiate1 a (c + k))
  | 0, B, F, c, h => by
    simp only [Expr.peelPis, Option.some.injEq] at h ⊢; rw [h]; rfl
  | k + 1, .forallE X Y, F, c, h => by
    have := peelPis_instantiate1 (a := a) k (c + 1) h
    simpa [Expr.instantiate1, Expr.peelPis, Nat.add_assoc, Nat.add_comm 1 k] using this
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _, _, _, h
  | _ + 1, .letE _ _ _, _, _, h | _ + 1, .lit _, _, _, h
  | _ + 1, .proj _ _ _, _, _, h => nomatch h

/-- One parameter substituted: the field telescope of the rest. -/
theorem unitFieldTele_cons {A B tele a : Expr} {as : List Expr} :
    unitFieldTele (.forallE A B) (as.length + 1) (a :: as) = some tele →
      unitFieldTele (B.instantiate1 a 0) as.length as = some tele := by
  rw [unitFieldTele_eq, unitFieldTele_eq]
  intro h
  cases hb : Expr.peelPis as.length B with
  | none => simp [Expr.peelPis, hb] at h
  | some F =>
    simp only [Expr.peelPis, hb, Option.map_some, Option.some.injEq,
      List.length_cons, Nat.add_sub_cancel] at h
    rw [peelPis_instantiate1 as.length 0 hb, Nat.zero_add]
    simp only [Option.map_some, Option.some.injEq]
    rw [← h]
    rfl

/-- No parameter: the constructor type itself. -/
theorem unitFieldTele_nil {cty tele : Expr} (h : unitFieldTele cty 0 [] = some tele) :
    tele = cty := by
  rw [unitFieldTele_eq] at h
  simp only [Expr.peelPis, Option.map_some, Option.some.injEq] at h
  rw [← h]; rfl

/-- A peel of a telescope bounded at `j` is bounded at `j + k`. -/
theorem looseBVarsBounded_peelPis :
    ∀ (k : Nat) {e r : Expr} {j : Nat}, e.looseBVarsBounded j = true →
      Expr.peelPis k e = some r → r.looseBVarsBounded (j + k) = true
  | 0, e, r, j, he, h => by
    simp only [Expr.peelPis, Option.some.injEq] at h; rw [← h]; exact he
  | k + 1, .forallE _ b, r, j, he, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he
    have := looseBVarsBounded_peelPis k he.2 h
    rwa [Nat.add_assoc, Nat.add_comm 1 k] at this
  | _ + 1, .bvar _, _, _, _, h | _ + 1, .fvar _ _, _, _, _, h | _ + 1, .sort _, _, _, _, h
  | _ + 1, .const _ _, _, _, _, h | _ + 1, .app _ _, _, _, _, h | _ + 1, .lam _ _, _, _, _, h
  | _ + 1, .letE _ _ _, _, _, _, h | _ + 1, .lit _, _, _, _, h
  | _ + 1, .proj _ _ _, _, _, _, h => nomatch h

/-- **The field telescope's frame**: a closed constructor type at closed
arguments gives a closed telescope whose leaves are the arguments'. -/
theorem unitFieldTele_frame {cty tele : Expr} {args : List Expr}
    (hc : cty.hasFvar = false) (hb : cty.looseBVarsBounded 0 = true)
    (hargs : ∀ a ∈ args, a.looseBVarsBounded 0 = true)
    (h : unitFieldTele cty args.length args = some tele) :
    tele.looseBVarsBounded 0 = true ∧
      ∀ l ∈ tele.fvarLeaves, ∃ a ∈ args, l ∈ a.fvarLeaves := by
  rw [unitFieldTele_eq] at h
  cases hp : Expr.peelPis args.length cty with
  | none => rw [hp] at h; exact nomatch h
  | some body =>
    rw [hp] at h
    obtain rfl := Option.some.inj h
    have hbb : body.looseBVarsBounded args.length = true := by
      simpa using looseBVarsBounded_peelPis args.length hb hp
    refine ⟨ConLeche.instSpine_closed hargs hbb, fun l hl => ?_⟩
    rcases fvarLeaves_instSpine _ hl with hl' | hl'
    · rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar (hasFvar_peelPis hc hp)] at hl'
      exact absurd hl' List.not_mem_nil
    · exact hl'

/-! ## The field telescope of an instance, read -/

/-- **The fit through the parameters**: a spine fitting the constructor's
telescope at the instance's parameter values fits, past them, the field
telescope with the parameters substituted. -/
theorem unitTele_fit {d : Nat} :
    ∀ (targs : List Expr) {cty : Expr} {Ca : Term} {tsa : List Term} {tele : Expr},
      unitFieldTele cty targs.length targs = some tele →
      denote m.acval env φ d cty = some Ca → Expr.fvarsBelow d cty →
      (∀ a ∈ targs, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      DenoteSpine m.acval env φ d targs tsa →
      ∃ telea : Term, denote m.acval env φ d tele = some telea ∧
        ∀ (ρ : Nat → V) (L : List V) (r : V), WellDenoted V ρ Ca →
          (∀ x ∈ tsa, WellDenoted V ρ x) →
          TeleFit V ρ Ca (tsa.map (interp V ρ) ++ L) r →
          WellDenoted V ρ telea ∧ TeleFit V ρ telea L r
  | [], cty, Ca, tsa, tele, h, hd, _, _, hsp => by
    cases hsp
    obtain rfl := unitFieldTele_nil h
    exact ⟨Ca, hd, fun _ _ _ hw _ hf => ⟨hw, by simpa using hf⟩⟩
  | a :: as, cty, Ca, tsa, tele, h, hd, hfb, hargs, hsp => by
    cases hsp with
    | @cons _ xa _ xs ha hsp' =>
    cases cty with
    | forallE A B =>
      have h' := unitFieldTele_cons (by simpa using h)
      obtain ⟨Aa, Ba, hAa, hBa, rfl⟩ := denote_forallE_inv hd
      obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
      have hfB : Expr.fvarsBelow d B := hfb.2
      have hdB : denote m.acval env φ d (B.instantiate1 a 0) = some (Ba.inst xa 0) := by
        rw [denote_beta (ty := A) m.acval_closed (acval_inst_self m) hfB hwa hba ha 0, hBa]
        rfl
      obtain ⟨telea, hdt, hfit⟩ := unitTele_fit as h' hdB
        (Expr.fvarsBelow_instantiate1_gen hwa.fvarsBelow 0 hfB)
        (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) hsp'
      refine ⟨telea, hdt, fun ρ L r hw hwts hf => ?_⟩
      have hwx : WellDenoted V ρ xa := hwts xa List.mem_cons_self
      rw [List.map_cons, List.cons_append] at hf
      cases hf with
      | cons hmem hf' =>
        rw [WellDenoted_pi] at hw
        have hwB : WellDenoted V (cons (interp V ρ xa) ρ) Ba := hw.2.2.1 _ hmem
        have hfit' := teleFit_inst0_of (piChain_of_teleFit hf') hf'
        have hwBi : WellDenoted V ρ (Ba.inst xa 0) := by
          refine (WellDenoted_inst V Ba xa 0 ρ (by rw [shiftE_zero_zero]; exact hwx)).mpr ?_
          rwa [shiftE_zero_zero, instE_zero]
        exact hfit ρ L r hwBi (fun x hx => hwts x (List.mem_cons_of_mem _ hx)) hfit'
    | _ => simp [unitFieldTele_eq, Expr.peelPis] at h

/-! ## A unit-like family instance -/

/-- A reduction of a type, at a valuation where the type is graded: the
reduct reads, is graded, and has the same value ("not pt" source (1)). -/
theorem red_ty_at {d : Nat} {T w : Expr} (hr : RedSem m φ d T w) {Δa : List Term} {Ta : Term}
    (hfT : Frame d T) (hCT : CtxOkS m φ d Δa T) (hdT : denote m.acval env φ d T = some Ta)
    {ρ : Nat → V} (hρ : Sat V Δa ρ) (hLT : LeavesGr m φ d T ρ) (hokT : WellDenotedTy V ρ Ta) :
    Frame d w ∧ CtxOkS m φ d Δa w ∧ LeavesGr m φ d w ρ ∧
      ∃ wa, denote m.acval env φ d w = some wa ∧ WellDenoted V ρ wa ∧
        interp V ρ Ta = interp V ρ wa := by
  obtain ⟨hfW, hsubW, wa, hwa, hY⟩ := hr hfT hCT hdT
  obtain ⟨hokW, heqW⟩ := hY ρ hρ hLT hokT.1 hokT.2.ne_pt
  exact ⟨hfW, hCT.of_subset hsubW, hLT.of_subset hsubW, wa, hwa, hokW, heqW⟩

/-- **An η family**: two members that are not the point are the
constructor at the parameters and their projections (none at a fieldless
family), which fit the field telescope (`unitTele_fit`) and so coincide
(`UnitFieldsSem`). -/
theorem UnitLike.struct_sound (hin : RulesInputs V m φ) {d n : Nat} {T w tele : Expr}
    (hr : RedSem m φ d T w) (hsh : unitLikeShape env w = some (tele, n))
    (hf : UnitFieldsSem m φ d tele n) :
    UnitLikeSem m φ d T := by
  intro hfT Δa Ta hCT hdT ρ hρ hLT hokT x y hx hy
  obtain ⟨hfW, hCW, hLW, wa, hwa, hokW, heqW⟩ := red_ty_at hr hfT hCT hdT hρ hLT hokT
  obtain ⟨S, us, cvS, caps, tbl, cvC, nPc, nFc, hfn, hfS, heta, hus, hT, hlen, hfC, rfl,
    htele⟩ := ConLeche.unitLikeShape_some hsh
  -- the table's laws, at every field count
  obtain ⟨⟨cvT', capsT', hfT', hlpsT', -⟩, hetaL⟩ := hin.tower_ok.table S tbl hT
  obtain ⟨rfl, rfl⟩ : cvS = cvT' ∧ caps = capsT' := by
    rw [hfS] at hfT'
    exact ConstantInfo.indInfo.inj (Option.some.inj hfT')
  obtain ⟨hlaw, hcoh⟩ := hetaL cvS caps hfS us (by rw [← hlpsT']; exact hus)
  obtain ⟨TCa, hTCa, hfitC⟩ := hcoh heta cvC nPc nFc hfC
  -- the table's constructor is stored at the table's levels
  obtain ⟨-, -, -, -, cvC', hfC', hlpsC, -⟩ := m.proj_ok S tbl hT
  obtain rfl : cvC = cvC' := by
    rw [hfC] at hfC'
    exact (ConstantInfo.ctorInfo.inj (Option.some.inj hfC')).1
  -- the constructor type's reading, at every depth
  obtain ⟨tc, htc, hoktc, -, -, -⟩ :=
    constTy_pkg hin.const_ty hfC (show us.length = _ by
      show us.length = cvC.levelParams.length; rw [hlpsC, ← hlpsT']; exact hus)
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at htc hoktc
  obtain rfl : TCa = tc := Option.some.inj (hTCa.symm.trans (htc 0))
  -- the instance: the family at its parameters
  rw [show w = Expr.mkAppN w.getAppFn w.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp w).symm, hfn] at hwa
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denote_mkAppN_inv hwa
  rw [denote, hfS] at hvT
  dsimp only at hvT
  split at hvT
  case isFalse => exact nomatch hvT
  case isTrue =>
  obtain rfl : vT = m.acval S (Level.substFn φ cvS.levelParams us) :=
    (Option.some.inj hvT).symm
  have hfold : ∀ (l : List Term) (z : V),
      l.foldl (fun r y => SetTheory.app r (interp V ρ y)) z
        = (l.map (interp V ρ)).foldl SetTheory.app z := by
    intro l z; rw [List.foldl_map]
  have hTy : IsTy (interp V ρ (Term.mkAppN (m.acval S (Level.substFn φ cvS.levelParams us)) tsa)) :=
    heqW ▸ hokT.2
  rw [heqW] at hx hy
  refine IsTy.eq_of_ne_pt hTy hx hy fun hnx hny => ?_
  rw [interp_mkAppN, hfold] at hx hy
  rw [hlpsT'] at hx hy
  have hfit : FamFit V ρ (m.acval S (Level.substFn φ tbl.levelParams us)) (tsa.map (interp V ρ)) :=
    ⟨tsa, rfl, by rw [← hlpsT']; exact hokW, by rw [← hlpsT', ← heqW]; exact hokT.2.ne_pt⟩
  have hlenP : (tsa.map (interp V ρ)).length = tbl.numParams := by
    rw [List.length_map, ← hspt.length, hlen]
  -- each member: the constructor at the parameters and its projections, fitting
  obtain ⟨rx, hfx⟩ := hfitC ρ _ x hlenP hfit hx hnx
  obtain ⟨ry, hfy⟩ := hfitC ρ _ y hlenP hfit hy hny
  -- the field telescope the checker walks
  have hargs : ∀ a ∈ w.getAppArgs, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true :=
    fun a ha => ⟨hfW.1.getAppArgs a ha, ConLeche.looseBVarsBounded_getAppArgs hfW.2.1 a ha⟩
  have hwfC := m.wf.consts _ (Env.find?_mem hfC)
  have hcl : (cvC.type.instantiateLevelParams cvC.levelParams us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwfC.1
  have htele' : unitFieldTele (cvC.type.instantiateLevelParams cvC.levelParams us)
      w.getAppArgs.length w.getAppArgs = some tele := by rw [hlen]; exact htele
  obtain ⟨telea, hdt, hpeel⟩ := unitTele_fit w.getAppArgs htele' (htc d)
    (Expr.WScoped.of_not_hasFvar (d := d) hcl).fvarsBelow hargs hspt
  obtain ⟨hwt, hfx'⟩ := hpeel ρ _ rx (hoktc ρ) (hoist_spineV tsa hokW).2 hfx
  obtain ⟨-, hfy'⟩ := hpeel ρ _ ry (hoktc ρ) (hoist_spineV tsa hokW).2 hfy
  obtain ⟨hbt, hlt⟩ := unitFieldTele_frame hcl
    (by rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hwfC.2.2.2.1)
    (fun a ha => (hargs a ha).2) htele'
  have hsubt : ∀ l ∈ tele.fvarLeaves, l ∈ w.fvarLeaves := fun l hl => by
    obtain ⟨a, ha, hla⟩ := hlt l hl
    exact ConLeche.fvarLeaves_getAppArgs ha l hla
  have hfte : Frame d tele :=
    ⟨unitFieldTele_WScoped hcl (fun a ha => (hargs a ha).1) htele', hbt,
      fun l hl => hfW.2.2 l (hsubt l hl)⟩
  have hproj := hf hfte (hCW.of_subset hsubt) hdt ρ hρ (hLW.of_subset hsubt) hwt _ _ _ _
    (by simp) (by simp) hfx' hfy'
  rw [hlaw ρ _ x hlenP hfit hx, hlaw ρ _ y hlenP hfit hy, hproj]

/-! ## Unit-likeness -/

/-- **Unit-likeness**: each side, not the point, is a member of its reduced
type (a family's application, or a ∀ at a neutral side, task #342 L18); the
two types are one, and unit-like. -/
theorem DefEq.unitLike_sound {d : Nat} {a ta wta b tb wtb : Expr}
    (hta : InferSemIO m φ d a ta) (hwta : RedSem m φ d ta wta) (hwtar : Red env d ta wta)
    (hnA : wta.isForallE = true → a.ioNeutral = true) (hu : UnitLikeSem m φ d wta)
    (htb : InferSemIO m φ d b tb) (hwtb : RedSem m φ d tb wtb) (hwtbr : Red env d tb wtb)
    (hnB : wtb.isForallE = true → b.ioNeutral = true) (hd : DefEqSem m φ d wta wtb) :
    DefEqSem m φ d a b := by
  intro hfa hfb Δa aa ba hCa hCb hda hdb ρ hρ hLa hLb hwa hwb hna hnb
  -- a side that is not the point is a member of its io-inferred type
  have hmem : ∀ {e te wte : Expr} {ea : Term}, InferSemIO m φ d e te → Red env d te wte →
      (wte.isForallE = true → e.ioNeutral = true) → Frame d e → CtxOkS m φ d Δa e →
      denote m.acval env φ d e = some ea → LeavesGr m φ d e ρ → WellDenoted V ρ ea →
      interp V ρ ea ≠ pt →
      Frame d te ∧ LeavesSub te e ∧ ∃ tea, denote m.acval env φ d te = some tea ∧
        WellDenotedTy V ρ tea ∧ interp V ρ ea ∈ˢ interp V ρ tea := by
    intro e te wte ea hte hr hn hfe hCe hde hLe hwe hne
    obtain ⟨hft, hsub, tea, htea, hX⟩ := hte hfe hCe hde
    refine ⟨hft, hsub, tea, htea, ?_⟩
    cases hF : wte.isForallE with
    | true =>
      rcases (hX ρ hρ hLe hwe).2 (hn hF) with h | h
      · exact absurd h hne
      · exact h.of_reading htea
    | false =>
      exact (IORel.mem_of_red (hX ρ hρ hLe hwe).1 hne hr
        (fun ty body h => by rw [h] at hF; exact nomatch hF)).of_reading htea
  obtain ⟨hfta, hsuba, taa, htaa, hokTa, hmA⟩ := hmem hta hwtar hnA hfa hCa hda hLa hwa hna
  obtain ⟨hftb, hsubb, tba, htba, hokTb, hmB⟩ := hmem htb hwtbr hnB hfb hCb hdb hLb hwb hnb
  have hCta : CtxOkS m φ d Δa ta := hCa.of_subset hsuba
  have hCtb : CtxOkS m φ d Δa tb := hCb.of_subset hsubb
  obtain ⟨hfWA, hCWA, hLWA, wtaa, hwtaa, hokWA, heqA⟩ :=
    red_ty_at hwta hfta hCta htaa hρ (hLa.of_subset hsuba) hokTa
  obtain ⟨hfWB, hCWB, hLWB, wtba, hwtba, hokWB, heqB⟩ :=
    red_ty_at hwtb hftb hCtb htba hρ (hLb.of_subset hsubb) hokTb
  have hEq : interp V ρ wtaa = interp V ρ wtba :=
    hd hfWA hfWB hCWA hCWB hwtaa hwtba ρ hρ hLWA hLWB hokWA hokWB
      (heqA ▸ hokTa.2.ne_pt) (heqB ▸ hokTb.2.ne_pt)
  exact hu hfWA hCWA hwtaa ρ hρ hLWA ⟨hokWA, heqA ▸ hokTa.2⟩ _ _ (heqA ▸ hmA)
    (by rw [hEq, ← heqB]; exact hmB)

end ConLeche.Model.Rules


