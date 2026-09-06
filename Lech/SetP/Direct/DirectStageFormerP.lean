import Lech.SetP.Direct.DirectDataP
import Lech.Verify.Direct.DirectInv

/-!
# The former's cons (task #175 W4c, P3 module 6, part 2)

`stageFormer`: the P step at the type former's cons, for a given
field chain `Fs`.  The leaf is `directTyAV (resSort.eval ψ) (pps ψ)
(Fs ψ)`; the chain's hereditary grading at the former's parameter
frame is the one premise the two installs of the former differ in —
the *dummy* install (`Fs = []`, whose premise is trivial) serves the
constructor-stage claims that grade the real chain, and the *real*
install builds the model the rest of the block extends.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

theorem stripPisAV_mkPisAV :
    ∀ (pps : List (Nat × Nat × AVExpr)) (b : AVExpr),
      stripPisAV pps.length (mkPisAV pps b) = some (pps, b)
  | [], _ => rfl
  | d :: pps, b => by
    simp only [List.length_cons, mkPisAV, stripPisAV, stripPisAV_mkPisAV pps b,
      Option.map_some]

/-! ## The former's hereditary premises -/

/-- **The former leaf's two hereditary premises**, from the former's
data and the field chain's grading at the parameter frame. -/
theorem formerWalks {m : EnvS2Core V env} {cvT : ConstantVal} {nP : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData m cvT nP resSort pps)
    {Fs : (Name → Nat) → List AVExpr}
    (hFsOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ →
      FieldsOkB (resSort.eval ψ) ρ (Fs ψ) ∧ FieldsValid ρ (Fs ψ))
    (ψ : Name → Nat) (ρ : Nat → V) :
    ParamsOkT (resSort.eval ψ) ρ (Fs ψ) (pps ψ) ∧
      UnderTowerValid ρ (towerBodyAV (resSort.eval ψ) (Fs ψ)) (pps ψ) := by
  have hst := stripPisAV_mkPisAV (pps ψ) (.sort (resSort.eval ψ))
  rw [hFD.len ψ] at hst
  have htele := piTeleP_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleP_graded (V := V) htele (Δ₀ := [])
    (fun ρ _ => hFD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hlenΓ : (((pps ψ).map (·.2.2)).reverse).length = nP := by
    simp [hFD.len ψ]
  have hent : ∀ i, i < nP → ∃ p, (pps ψ)[i]? = some p ∧
      p.2.2 = (((pps ψ).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
    intro i hi
    have hil : i < (pps ψ).length := by rw [hFD.len ψ]; exact hi
    refine ⟨(pps ψ)[i], List.getElem?_eq_getElem hil, ?_⟩
    rw [getD_reverse_of_peel (hFD.len ψ) hi (List.getElem?_eq_getElem hil)]
  have hΓnil : (((pps ψ).map (·.2.2)).reverse).drop (nP - 0) = [] := by
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlenΓ]; exact Nat.le_refl _)]
  constructor
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => ParamsOkT (resSort.eval ψ) ρ (Fs ψ) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => (hFsOk ψ ρ hρ).1)
      (fun ρ d ds hd hok hrec => ⟨hFD.bits ψ d hd, hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat2_nil V ρ)
    simpa using hw
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => UnderTowerValid ρ (towerBodyAV (resSort.eval ψ) (Fs ψ)) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => towerBodyAV_validV (hFsOk ψ ρ hρ).2)
      (fun ρ d ds hd hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat2_nil V ρ)
    simpa using hw

/-! ## The cons -/

/-- **The P step at the former's cons**, for a given field chain. -/
theorem stageFormer (mp : EnvS2PM V μ env)
    (hE₀ : Lech.EtaFamiliesClosed env)
    {F : Nat} {p : DirectParts} {envI : Env} {cvTa : ConstantVal}
    (hind : Lech.checkDirectInd (Lech.fueledOps μ F) env p = .ok (envI, cvTa))
    -- the constructor's name is fresh at the extension (it is checked
    -- there next), so the block's family is not yet η-complete
    (hCfresh : envI.find? p.cvC.name = none)
    {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (Fs : (Name → Nat) → List AVExpr)
    (hFsParams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) → Fs ψ₁ = Fs ψ₂)
    (hFsBelow : ∀ ψ : Name → Nat, FieldsBelow p.nP (Fs ψ))
    (hFsOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ →
      FieldsOkB (p.resSort.eval ψ) ρ (Fs ψ) ∧ FieldsValid ρ (Fs ψ))
    (hFs0 : p.nF = 0 → ∀ ψ, Fs ψ = []) :
    ∃ mp' : EnvS2PM V μ envI,
      mp'.base2.acval = acvalWith mp.base2.acval cvTa.name
        (fun ψ => directTyAV (p.resSort.eval ψ) (pps ψ) (Fs ψ)) := by
  obtain ⟨hccv, rfl, -⟩ := Lech.checkDirectInd_shape hind
  obtain ⟨hfind, hnres, hpshape, -, -, -, type', -, -, -, -, htr', -, -, hty⟩ :=
    Lech.checkConstantVal_inv hccv
  have hname : cvTa.name = p.cvT.name := by rw [hty]
  have hfresh : env.find? cvTa.name = none := by
    rw [hname]; exact hfind
  have htr : cvTa.type.constsResolve env = true := by rw [hty]; exact htr'
  have hcb : ConstsBound env cvTa.type := constsBound_of_constsResolve _ htr
  obtain ⟨hwfI, -⟩ := Lech.direct_ind_wf mp.base2.wf hind
  -- the leaf
  let A : (Name → Nat) → AVExpr :=
    fun ψ => directTyAV (p.resSort.eval ψ) (pps ψ) (Fs ψ)
  have hAbelow : ∀ ψ, VExpr.bvarsBelow 0 (A ψ).erase := fun ψ =>
    directTyAV_below (hFD.below ψ)
      (by rw [hFD.len ψ, Nat.zero_add]; exact hFsBelow ψ)
  have hwalks := formerWalks hFD hFsOk
  -- the reading at the extension
  have hreadI : ∀ ψ : Name → Nat,
      denoteP (acvalWith mp.base2.acval cvTa.name A)
        ⟨.indInfo cvTa (Lech.directCaps p) :: env.consts⟩ ψ 0 cvTa.type
        = some (mkPisAV (pps ψ) (.sort (p.resSort.eval ψ))) := fun ψ =>
    denoteP_cons_mono (c₀ := .indInfo cvTa (Lech.directCaps p)) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hFD.read ψ)
  have hnresI : Lech.reservedBasisNames.contains
      (ConstantInfo.indInfo cvTa (Lech.directCaps p)).name = false := by
    show Lech.reservedBasisNames.contains cvTa.name = false
    rw [hname]; exact hnres
  have hpshapeI : (ConstantInfo.indInfo cvTa (Lech.directCaps p)).name.isProjFnShape
      = false := by
    show cvTa.name.isProjFnShape = false
    rw [hname]; exact hpshape
  refine declStepPM_of_ind_member_cons mp (c₀ := .indInfo cvTa (Lech.directCaps p))
    (A := A) hfresh hnresI (Or.inl ⟨_, _, rfl⟩)
    (ConsHeadP.ofFresh hwfI (fun ψ => hAbelow ψ) hnresI
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- level dependence
    intro ψ₁ ψ₂ hφ
    obtain ⟨hp, hw⟩ := hFD.params ψ₁ ψ₂ hφ
    show directTyAV _ _ _ = directTyAV _ _ _
    rw [hp, hw, hFsParams ψ₁ ψ₂ hφ]
  · exact fun ψ ρ => directTyAV_ok2 (hwalks ψ ρ).1
  · exact fun ψ ρ => (directTyAV_okP (hwalks ψ ρ).1 (hwalks ψ ρ).2).2
  · exact fun ψ => ⟨_, hreadI ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact hFD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact directTyAV_mem (hwalks ψ ρ).1
  · -- `caps_ok`: the prefix families cross; the block's own family is
    -- not η-complete yet (its constructor is fresh) and is unit-like
    -- exactly when fieldless
    intro m₂ hac
    refine capsOkP_cons_direct mp (c₀ := .indInfo cvTa (Lech.directCaps p))
      (A := A) (T := cvTa.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeI
      (Or.inl ⟨cvTa, Lech.directCaps p, rfl, rfl⟩)
      (fun T' cvT' caps' hf _ hres hcape => hE₀ T' cvT' caps' hf hcape hres)
      m₂ hac ?_
    intro cvT caps hf hres
    have hself := Lech.Env.find?_cons_self
      (ConstantInfo.indInfo cvTa (Lech.directCaps p)) env
    obtain ⟨rfl, rfl⟩ :=
      ConstantInfo.indInfo.inj (Option.some.inj (hself.symm.trans hf))
    refine ⟨fun _ hfam => ?_, fun hunit φ' => ?_⟩
    · -- η-complete would store the constructor, which is fresh
      exfalso
      obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
      rw [show (Lech.directCaps p).etaCtor = p.cvC.name from rfl, hCfresh] at hfC
      exact nomatch hfC
    · have hnF : p.nF = 0 := by
        have : (p.nF == 0) = true := hunit
        simpa using this
      have hFD₂ : FormerData m₂ cvTa p.nP p.resSort pps :=
        hFD.cross (c₀ := .indInfo cvTa (Lech.directCaps p)) (A := A) hfresh
          (ConsCrossAt.ofNtc fun _ h => nomatch h) hcb m₂ hac
      refine directUnitLawP (m := m₂) (T := cvTa.name) (caps := Lech.directCaps p)
        ?_ hFD₂.read hFD₂.okTy ?_ ?_
      · intro ψ
        rw [hac]
        show acvalWith mp.base2.acval cvTa.name A cvTa.name ψ = _
        rw [acvalWith_self]
        show directTyAV _ _ (Fs ψ) = _
        rw [hFs0 hnF ψ]
      · intro ψ ρ
        have := (hwalks ψ ρ).1
        rwa [hFs0 hnF ψ] at this
      · intro ψ
        show p.nP = (pps ψ).length
        rw [hFD.len ψ]

end Lech.SetP
