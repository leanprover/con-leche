module

public import ConLeche.Model.Rules.Inputs
public import ConLeche.Model.CtxOkP
public import ConLeche.Model.Env.EnvModelM
public import ConLeche.Verify.Rules.Refine
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Inductives.TypeStep
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.NestPosRed
import ConLeche.Semantics.Frame
import ConLeche.Verify.Abstract
import ConLeche.Verify.Leaves
import ConLeche.Verify.Shift
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Verify.Denote.ConstsBound
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Env.CanonCrest
import ConLeche.Model.Capstone

public section

/-!
# A family's telescope, run, read in a model

A stored former whose declared type does not show its telescope has it read at use, by a run
of the telescope walk (`familyTelescope`) at the environment of the use.  The run is a
telescope of reductions there (`whnfTelescope_teleRed`), each sound in that environment's
model (`red_sound_ty`, at the binders opened at free variables): its result reads as a Π-tower
over a sort of the run's length, a graded type of the declared type's value
(`familyTelescope_read`).  Nothing about the block that recorded the family is read: the run's
result is compared with the block's telescope by value, along fits
(`spineFit_iff_of_mkPisAV_eq`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules

open ConLeche (Env Expr Name Level ConstantVal IndCaps closeTelescope fueledOps)
open ConLeche.Rules (TeleRed)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- **A telescope of reductions reads like its subject**: a graded type `e` that reduces, binder
by binder, to the Π-tower over `bs` ending in the sort `s` has the closed telescope reading as a
Π-tower of `n` binders over `s`'s value, graded, of `e`'s value at every satisfying frame. -/
theorem teleRed_read (hin : RulesInputs V m φ) :
    ∀ (i n : Nat) (e : Expr) (bs : List Expr) (s : Level), TeleRed env i n e bs s →
      Frame i e → ∀ {Δa : List Term} {ea : Term}, CtxOkP m φ i Δa e →
      denote m.acval env φ i e = some ea → GradedTy V Δa ea →
      ∃ ab : List Term,
        denote m.acval env φ i (closeTelescope bs i (.sort s))
          = some (mkPisAV ab (.sort (s.eval φ))) ∧
        ab.length = n ∧ GradedTy V Δa (mkPisAV ab (.sort (s.eval φ))) ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ (mkPisAV ab (.sort (s.eval φ)))) ∧
        Frame i (closeTelescope bs i (.sort s)) ∧ LeavesSub (closeTelescope bs i (.sort s)) e
  | i, 0, e, [], s, ht, hfr, Δa, ea, hC, hea, hgr => by
    obtain ⟨hfr', hsub, ea', hea', hg', heq⟩ := red_sound_ty hin ht hfr hC.toCtxOk hea hgr
    rw [denote_sort] at hea'
    obtain rfl := Option.some.inj hea'
    exact ⟨[], by simp [closeTelescope, mkPisAV, denote_sort], rfl, by simpa [mkPisAV] using hg',
      by simpa [mkPisAV] using heq, by simpa [closeTelescope] using hfr',
      by simpa [closeTelescope] using hsub⟩
  | i, n + 1, e, dom :: bs, s, ht, hfr, Δa, ea, hC, hea, hgr => by
    obtain ⟨body, hr, hrest⟩ := ht
    obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ := red_sound_ty hin hr hfr hC.toCtxOk hea hgr
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denote_forallE_inv hwa
    obtain ⟨hws, hb, hLb⟩ := hfrw
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hLa : Expr.LeavesBounded dom := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded body := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgAT, hgB⟩ := WellDenoted.hoist_piTy' (V := V) hgw.graded
    have hCw : CtxOkP m φ i Δa (.forallE dom body) := hC.of_subset hsub
    have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgAT
    obtain ⟨ab, hrd, hlen, hgn, heqn, hfrn, hsubn⟩ :=
      teleRed_read hin (i + 1) n _ bs s hrest (frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd) hCop
        hba hgB
    obtain ⟨hwsn, hbn, hLn⟩ := hfrn
    have hbnd : (closeTelescope bs (i + 1) (.sort s)).looseBVarsBounded 0 = true := hbn
    refine ⟨ta :: ab, ?_, by simp [hlen], ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [closeTelescope]
      rw [denote_forallE, hta]
      simp only [bind, Option.bind]
      rw [denote_erasedEq (erasedEq_abstract1_instantiate1 _ 0 hbnd), hrd]
      rfl
    · exact gradedTy_pi_intro (GradedTy.graded hgAT) hgn.graded (fun ρ hρ => (hgAT ρ hρ).2)
        (fun ρ hρ => (hgn ρ hρ).2)
    · intro ρ hρ
      rw [heq ρ hρ]
      simp only [interp_pi, mkPisAV]
      exact piV_congr fun x hx => heqn _ (Sat_cons V hρ hx)
    · simp only [closeTelescope, Expr.WScoped]
      exact ⟨hws.1, WScoped.abstract1 0 hwsn⟩
    · simp only [closeTelescope, Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hb.1, looseBVarsBounded_abstract1 _ 0 hbnd⟩
    · intro l hl
      simp only [closeTelescope, Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hLa l hl
      · exact hLn l (Expr.fvarLeaves_abstract1_lt _ 0 hwsn l hl).1
    · intro l hl
      simp only [closeTelescope, Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hsub l (by simp [Expr.fvarLeaves, hl])
      · obtain ⟨hl₁, hl₂⟩ := Expr.fvarLeaves_abstract1_lt _ 0 hwsn l hl
        rcases Expr.fvarLeaves_instantiate1 body 0 (hsubn l hl₁) with h3 | h3
        · exact hsub l (by simp [Expr.fvarLeaves, h3])
        · simp only [Expr.fvarLeaves, List.mem_cons] at h3
          rcases h3 with rfl | h3
          · exact absurd hl₂ (by simp)
          · exact hsub l (by simp [Expr.fvarLeaves, h3])
  | _, 0, _, _ :: _, _, ht, _, _, _, _, _, _ => nomatch ht
  | _, _ + 1, _, [], _, ht, _, _, _, _, _, _ => nomatch ht

/-- **A family's telescope, run, in the model** (see the module docstring): at a stored former
whose declared type does not show its telescope, a successful run's result is closed, names
stored constants only, and reads at every level assignment as a Π-tower of the family's
parameters and indices over a sort, a graded type of the declared type's value. -/
theorem familyTelescope_read (mp : EnvModelM V env) {n : Name} {cv : ConstantVal}
    {caps : IndCaps} (hf : env.find? n = some (.indInfo cv caps))
    (hdh : ConLeche.formerDefHeaded cv = true) {F : Nat} {ty : Expr}
    (hrun : ConLeche.familyTelescope (fueledOps .verified F) env cv caps = .ok ty)
    (hin : ∀ ψ : Name → Nat, RulesInputs V mp.base2 ψ) :
    ty.hasFvar = false ∧ ty.looseBVarsBounded 0 = true ∧ ConstsBound env ty ∧
      ∀ ψ : Name → Nat, ∃ (ta₀ : Term) (ab : List Term) (u : Nat),
        denote mp.base2.acval env ψ 0 cv.type = some ta₀ ∧
        denote mp.base2.acval env ψ 0 ty = some (mkPisAV ab (.sort u)) ∧
        ab.length = caps.nparams + caps.nIdx ∧
        ∀ ρ : Nat → V, interp V ρ ta₀ = interp V ρ (mkPisAV ab (.sort u)) ∧
          WellDenotedTy V ρ (mkPisAV ab (.sort u)) := by
  rcases ConLeche.familyTelescope_cases hrun with ⟨hfl, -⟩ | ⟨-, cvR, hr, rfl⟩
  · rw [hdh] at hfl; exact nomatch hfl
  unfold ConLeche.reducedFormer at hr
  cases hw : ConLeche.whnfTelescope (fueledOps .verified F) env 0 (caps.nparams + caps.nIdx)
      cv.type with
  | error _ => rw [hw] at hr; exact nomatch hr
  | ok p =>
    rw [hw] at hr
    obtain ⟨bs, s⟩ := p
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hr
    subst hr
    have hT := ConLeche.Rules.whnfTelescope_teleRed 0 _ _ bs s hw
    have hmem := ConLeche.Env.find?_mem hf
    have hwf := mp.base2.wf.consts _ hmem
    have hcf : cv.type.hasFvar = false := hwf.1
    have hnl : cv.type.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hcf
    have hfr : Frame 0 cv.type := ⟨Expr.WScoped.of_not_hasFvar hcf, hwf.2.2.2.1, fun l hl => by
      rw [hnl] at hl; exact absurd hl List.not_mem_nil⟩
    have hC : ∀ ψ, CtxOkP mp.base2 ψ 0 [] cv.type := fun _ =>
      ⟨rfl, fun l hl => by rw [hnl] at hl; exact absurd hl List.not_mem_nil⟩
    have hrd : ∀ ψ, ∃ ta₀, denote mp.base2.acval env ψ 0 cv.type = some ta₀ ∧
        GradedTy V [] ta₀ := fun ψ => by
      obtain ⟨ta₀, h⟩ := mp.type_reads _ hmem ψ
      exact ⟨ta₀, h, fun ρ _ => mp.type_wellDenotedTy _ hmem ψ _ h ρ⟩
    obtain ⟨ta₀, hta₀, hg₀⟩ := hrd (fun _ => 0)
    obtain ⟨ab, hab, -, -, -, ⟨hws, hbb, hLs⟩, -⟩ :=
      teleRed_read (hin fun _ => 0) 0 _ _ bs s hT hfr (hC _) hta₀ hg₀
    have hnf : (closeTelescope bs 0 (.sort s)).hasFvar = false :=
      ConLeche.Expr.not_hasFvar_of_fvarsBelow_zero hws.fvarsBelow
    refine ⟨hnf, hbb, constsBound_of_read 0 _ hab fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl; exact absurd hl List.not_mem_nil,
      fun ψ => ?_⟩
    obtain ⟨ta₀, hta₀, hg₀⟩ := hrd ψ
    obtain ⟨ab, hab, hlen, hg, heq, -, -⟩ :=
      teleRed_read (hin ψ) 0 _ _ bs s hT hfr (hC ψ) hta₀ hg₀
    exact ⟨ta₀, ab, _, hta₀, hab, hlen, fun ρ =>
      ⟨heq ρ (Sat_nil V ρ), hg ρ (Sat_nil V ρ)⟩⟩

/-- **A run's result, read against its block** (`familyRead`): closed, naming stored constants
only, and at every level assignment a graded Π-tower over a sort of the length of the block's
telescope for the member and of its value. -/
@[expose] def FormerRead (mp : EnvModelM V env) (D : LfpDatum V) (mm : Nat) (ty : Expr) : Prop :=
  ty.hasFvar = false ∧ ty.looseBVarsBounded 0 = true ∧ ConstsBound env ty ∧
    ∀ ψ : Name → Nat, ∃ (ab : List Term) (u : Nat),
      denote mp.base2.acval env ψ 0 ty = some (mkPisAV ab (.sort u)) ∧
      ab.length = (D.pars mm ψ ++ D.ids mm ψ).length ∧
      ∀ ρ : Nat → V, interp V ρ (mkPisAV ab (.sort u))
          = interp V ρ (mkPisAV (D.pars mm ψ ++ D.ids mm ψ) (.sort (D.w ψ))) ∧
        WellDenotedTy V ρ (mkPisAV ab (.sort u))

/-- **What a run reads of a recorded family's telescope** has the block's telescope's value
(see the module docstring), for every member alike: a former that shows its telescope is its
own run's result. -/
theorem familyRead (mp : EnvModelM V env) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat}
    (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {F : Nat} {ty : Expr}
    (hrun : ConLeche.familyTelescope (fueledOps .verified F) env cv caps = .ok ty) :
    FormerRead mp D mm ty := by
  obtain ⟨cv', caps', hf', hflat, hval⟩ := mp.lfpReadsV hD mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  obtain ⟨-, -, -, -, ⟨hcp, -⟩⟩ := mp.lfp_ok D hD
  have hlen : ∀ ψ, (D.pars mm ψ ++ D.ids mm ψ).length = caps.nparams + caps.nIdx := by
    obtain ⟨cv', caps', hf', -, hl⟩ := hcp mm hmm
    rw [hf] at hf'
    obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
    exact hl
  -- the run's own reading: a tower of the declared type's value
  have hown : ty.hasFvar = false ∧ ty.looseBVarsBounded 0 = true ∧ ConstsBound env ty ∧
      ∀ ψ : Name → Nat, ∃ (ta₀ : Term) (ab : List Term) (u : Nat),
        denote mp.base2.acval env ψ 0 cv.type = some ta₀ ∧
        denote mp.base2.acval env ψ 0 ty = some (mkPisAV ab (.sort u)) ∧
        ab.length = caps.nparams + caps.nIdx ∧
        ∀ ρ : Nat → V, interp V ρ ta₀ = interp V ρ (mkPisAV ab (.sort u)) ∧
          WellDenotedTy V ρ (mkPisAV ab (.sort u)) := by
    rcases ConLeche.familyTelescope_cases hrun with ⟨hfl, rfl⟩ | ⟨hdh, -⟩
    · have hmem := ConLeche.Env.find?_mem hf
      have hwf := mp.base2.wf.consts _ hmem
      refine ⟨hwf.1, hwf.2.2.2.1, (ConLeche.Verify.envWF_constsBound mp.base2.wf _ hmem).1,
        fun ψ => ?_⟩
      obtain ⟨ab, u, hta, hl⟩ := hflat hfl ψ
      exact ⟨_, ab, u, hta, hta, hl, fun ρ =>
        ⟨rfl, mp.type_wellDenotedTy _ hmem ψ _ hta ρ⟩⟩
    · exact familyTelescope_read mp hf hdh hrun fun ψ => Rules.RulesInputs.ofSem mp ψ
  obtain ⟨h1, h2, h3, hrd⟩ := hown
  refine ⟨h1, h2, h3, fun ψ => ?_⟩
  obtain ⟨ta₀, ab, u, hta₀, hty, hl, hv⟩ := hrd ψ
  obtain ⟨ta₀', hta₀', hv'⟩ := hval ψ
  rw [hta₀] at hta₀'
  obtain rfl := Option.some.inj hta₀'
  exact ⟨ab, u, hty, by rw [hl, hlen], fun ρ => ⟨((hv ρ).1.symm.trans (hv' ρ).1), (hv ρ).2⟩⟩

end ConLeche.Model
