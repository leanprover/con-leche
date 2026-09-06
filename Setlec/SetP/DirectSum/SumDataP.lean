import Setlec.SetP.Direct.DirectCtorFramesP
import Setlec.SetP.DirectSum.SumIntroP
import Setlec.Verify.Direct.SumInv

/-!
# The direct sum's constructor data and frames (task #175 sum-types)

`sumCtorData_of` and `sumCtorFrames`: `ctorData_of`/`ctorFrames` with
the constructor's stage run taken from `checkDirectSumCtor` (one
constructor, made explicit) instead of `checkDirectCtor`'s
`DirectParts`.  The proofs are the structure route's verbatim: the
inversion `checkDirectSumCtor_shape` exposes the same runs.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- The constructor's data, from its stage run at the environment
holding the former. -/
theorem sumCtorData_of (hμ : μ.verifiedChecks = true) (mp : EnvS2PM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env} {caps : IndCaps}
    {bs : List (Name × Expr × Setlec.BinderMeta)}
    (hCtor : Setlec.checkDirectSumCtor (Setlec.fueledOps μ F) env₀ env T lps nP resSort
      isProp large cvC nF cvTa = .ok cvCa)
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hstripT : cvTa.type.stripPis nP = some (bs, .sort resSort)) :
    ∃ ds : (Name → Nat) → List (Nat × Nat × AVExpr),
      CtorData mp.base2 T cvCa nP nF resSort ds := by
  obtain ⟨hccv, -, fvsP, crest, tfvs, trest, xFvs, sorts, hopC, -, -, hopX, -, -⟩ :=
    Setlec.checkDirectSumCtor_shape hCtor
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', htp', -, hst,
    hens, rfl⟩ := Setlec.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' htp' hst hens hopC
  have hw : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hL : Expr.LeavesBounded type' := Expr.LeavesBounded.of_not_hasFvar htf'
  have hnil : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add nP hopC (by rw [Nat.zero_add]; exact hopX)
  have hidx := openPisAtFvars_index nP type' 0 hopC
  obtain ⟨F', tb, vb, hib, hensb, -, hbits⟩ :=
    piBits_of_infer hμ (nP + nF) hopAll hst hens
  rw [Nat.zero_add] at hib hensb
  obtain ⟨tf, htf⟩ := inferTypeCore_mkAppN_fn_inv fvsP hib
  obtain ⟨ci, hfci, -, rfl⟩ := Setlec.inferTypeCore_const_inv htf
  obtain rfl : ci = .indInfo cvTa caps := Option.some.inj (hfci.symm.trans hfT)
  have htfT : Setlec.inferTypeCore μ env F' (nP + nF)
      (.const T (lps.map .param)) = .ok cvTa.type := by
    have := htf
    rw [show (ConstantInfo.indInfo cvTa caps).toConstantVal = cvTa from rfl,
      hlpsT, Expr.instantiateLevelParams_self] at this
    exact this
  obtain rfl := inferTypeCore_mkAppN_sort fvsP htfT (by rw [hlenP]; exact hstripT) hib
  have hvb := ensureSortCore_sort_eq hensb
  rw [hvb] at hbits
  have hper : ∀ ψ : Name → Nat, ∃ ds : List (Nat × Nat × AVExpr),
      denoteP mp.base2.acval env ψ 0 type'
        = some (mkPisAV ds (ctorBodyAV mp.base2 T nP nF ψ)) ∧
      ds.length = nP + nF ∧
      (∀ d ∈ ds, (resSort.eval ψ = 0 ↔ d.2.1 = 0)) ∧
      (∀ ρ : Nat → V,
        AnnotOkP V ρ (mkPisAV ds (ctorBodyAV mp.base2 T nP nF ψ))) ∧
      DomsBelow 0 ds := by
    intro ψ
    have hc := claimsAtP_of hμ mp ψ F
    obtain ⟨Ta, hTa⟩ := acceptedReadsP_of mp.base2 ψ hst hw hbt' hL
    obtain ⟨-, -, hokT, -, -⟩ := hc.inferRow hst hw hbt' hL (CtxOkP.nil hnil) hTa
    have hokT' : ∀ ρ : Nat → V, AnnotOkP V ρ Ta := fun ρ =>
      hokT ρ (Sat2_nil V ρ)
    obtain ⟨Γ, R, htele, hop'⟩ := openedP_of hopAll htf' hbt' hTa hokT'
    have hR : R = ctorBodyAV mp.base2 T nP nF ψ := by
      have hb := hop'.body
      have hsp := denoteSpineP_indexed (acval := mp.base2.acval) (env := env)
        (φ := ψ) (d := nP + nF) fvsP 0 hidx
      have hconst := denoteP_const (acval := mp.base2.acval) (env := env) (φ := ψ)
        (d := nP + nF) hfT
        (show (lps.map Level.param).length
          = (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams.length by
          show (lps.map Level.param).length = cvTa.levelParams.length
          rw [hlpsT, List.length_map])
      rw [denoteP_mkAppN hsp hconst] at hb
      have hsubst : Level.substFn ψ (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams
          (lps.map Level.param) = ψ := by
        show Level.substFn ψ cvTa.levelParams (lps.map Level.param) = ψ
        rw [hlpsT]
        exact Level.substFn_param_self ψ _
      rw [hsubst, hlenP] at hb
      have : ctorBodyAV mp.base2 T nP nF ψ
          = AVExpr.mkAppN (mp.base2.acval T ψ)
            ((List.range nP).map fun j => AVExpr.bvar (nP + nF - 1 - (0 + j))) := by
        unfold ctorBodyAV paramBvars
        congr 1
        apply List.map_congr_left
        intro k _
        rw [Nat.zero_add]
      rw [this]
      exact (Option.some.inj hb).symm
    subst hR
    obtain ⟨ds, hst', -⟩ := stripPisAV_of_piTeleP htele
    obtain ⟨hTeq, hlen⟩ := stripPisAV_eq_mkPis hst'
    subst hTeq
    refine ⟨ds, hTa, hlen, ?_, hokT', ?_⟩
    · intro d hd
      exact (stripPisAV_bits (nP + nF) (hbits ψ) hTa hst' d hd).symm
    · exact (stripPisAV_below hst' (bvarsBelow_of_reading hw hbt' hTa)).1
  refine ⟨fun ψ => Classical.choose (hper ψ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun ψ => (Classical.choose_spec (hper ψ)).1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.1
  · exact fun ψ => (Classical.choose_spec (hper ψ)).2.2.2.2
  · intro ψ₁ ψ₂ hφ
    have h2 := (Classical.choose_spec (hper ψ₂)).1
    have h1 : denoteP mp.base2.acval env ψ₂ 0 type'
        = some (mkPisAV (Classical.choose (hper ψ₁))
          (ctorBodyAV mp.base2 T nP nF ψ₁)) := by
      rw [← denoteP_params_ext mp.base2 hφ 0 type' htp']
      exact (Classical.choose_spec (hper ψ₁)).1
    exact (mkPisAV_inj
      (by rw [(Classical.choose_spec (hper ψ₁)).2.1,
        (Classical.choose_spec (hper ψ₂)).2.1])
      (Option.some.inj (h1.symm.trans h2))).1

/-- **The constructor's frames**: the two parameter frames identified
and the field chain graded at the constructor's (`ctorFrames` from
the sum stage's run). -/
theorem sumCtorFrames (hμ : μ.verifiedChecks = true) (mp : EnvS2PM V μ env)
    {F : Nat} {T : Name} {lps : List Name} {nP nF : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env} {caps : IndCaps}
    (hCtor : Setlec.checkDirectSumCtor (Setlec.fueledOps μ F) env₀ env T lps nP resSort
      isProp large cvC nF cvTa = .ok cvCa)
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hProp : isProp = true → (Level.isEquiv resSort .zero == some true) = true)
    {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa nP resSort pps)
    {ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hCD : CtorData mp.base2 T cvCa nP nF resSort ds) :
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        (isProp = false →
          FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2))) ∧
        (isProp = true → large = true →
          FieldsBound 0 ρ (((ds ψ).drop nP).map (·.2.2)))) := by
  obtain ⟨hccv, -, fvsP, crest, tfvs, trest, xFvs, sorts, hopC, hopT, hdoms, hopX,
    -, hsorts⟩ := Setlec.checkDirectSumCtor_shape hCtor
  obtain ⟨-, -, -, -, hlbt, hitf, type', -, -, hann', -, -, -, -, rfl⟩ :=
    Setlec.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' hopC hsorts
  have hlenP : fvsP.length = nP := openPisAtFvars_length _ hopC
  have hopAll := openPisAtFvars_add nP hopC (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf _ (Setlec.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  obtain ⟨hlenS, hfields⟩ := Setlec.checkDirectFieldSorts_inv hsorts
  have hpins := Setlec.checkDirectDomsAt_inv hdoms
  have hlenX : xFvs.length = nF := openPisAtFvars_length _ hopX
  have hframes : ∀ ψ : Name → Nat,
      (∀ ρ : Nat → V, Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ) ∧
      ∀ ρ : Nat → V, Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        (isProp = false →
          FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2))) ∧
        (isProp = true → large = true →
          FieldsBound 0 ρ (((ds ψ).drop nP).map (·.2.2))) := by
    intro ψ
    have hc := claimsAtP_of hμ mp ψ F
    have hT : OpenedP mp.base2 ψ nP cvTa.type tfvs trest
        ((pps ψ).map (·.2.2)).reverse (.sort (resSort.eval ψ)) :=
      openedP_of_peel hopT hTf hTb (hFD.read ψ) (hFD.len ψ) (hFD.okTy ψ)
    have hC : OpenedP mp.base2 ψ (nP + nF) type' (fvsP ++ xFvs)
        (Expr.mkAppN (.const T (lps.map .param)) fvsP)
        ((ds ψ).map (·.2.2)).reverse (ctorBodyAV mp.base2 T nP nF ψ) :=
      openedP_of_peel hopAll htf' hbt' (hCD.read ψ) (hCD.len ψ) (hCD.okTy ψ)
    have hpf := paramFrames hc hT hC (fun i hi => by
      obtain ⟨a, b, ha, hb, hdeq⟩ := hpins i hi
      rw [List.getElem?_map] at hb
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨a, b', by rw [List.getElem?_append_left (by omega)]; exact ha, hb',
        by rw [Nat.zero_add] at hdeq; exact hdeq⟩)
    have hlenDs := hCD.len ψ
    have hlenF : ((((ds ψ).drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
    have hiff : ∀ ρ : Nat → V, Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ := by
      intro ρ
      have := (hpf nP (Nat.le_refl _)).1 ρ
      rw [drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero,
        List.drop_zero] at this
      exact this.symm
    refine ⟨hiff, fun ρ hρ => ?_⟩
    have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = nP + nF := by
      simp [hlenDs]
    have hρ' : Sat2 V ((((ds ψ).map (·.2.2)).reverse).drop (nP + nF - (nP + 0))) ρ := by
      rw [show nP + nF - (nP + 0) = nP + nF - nP from by omega,
        drop_fields_eq hlenDs nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
      exact hρ
    have hrow : ∀ j, j < nF → ∃ u, sorts[j]? = some u ∧
        (isProp = false → Level.leq u resSort = some true) ∧
        (isProp = true → large = true →
          (Level.isEquiv u .zero == some true) = true) ∧
        ∀ ρ : Nat → V,
          Sat2 V ((((ds ψ).map (·.2.2)).reverse).drop (nP + nF - (nP + j))) ρ →
          interp2 V ρ ((((ds ψ).map (·.2.2)).reverse).getD
            (nP + nF - 1 - (nP + j)) default) ∈ˢ (univ (u.eval ψ) : V) := by
      intro j hj
      obtain ⟨fv, ty, u, hfv, hu, hi, hens, hleq, hz⟩ := hfields j hj
      refine ⟨u, hu, hleq, hz, fun ρ hρ => ?_⟩
      have hfvA : (fvsP ++ xFvs)[nP + j]? = some fv := by
        rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
        exact hfv
      obtain ⟨-, hws, hb, hL, hleaf⟩ := hC.var (nP + j) fv hfvA
      have hCtx := hC.ctx (i := nP + j) (by omega) hws hleaf
      have hread := hC.doms (nP + j) fv hfvA
      exact (hc.sortRow hi hens hws hb hL hCtx hread ρ hρ).2
    have hFsEq := fieldsFrom_eq_drop (ds := ds ψ) (nP := nP) (nF := nF) hlenDs
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hFsEq]
      refine fieldsOkB_of_frame rfl hΓlen hC.okΓ ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ hw
      obtain ⟨u, -, hleq, -, hmem⟩ := hrow j hj
      by_cases hnp : isProp = true
      · exfalso
        have h0 := Level.isEquiv_sound (beq_iff_eq.mp (hProp hnp)) ψ
        exact hw (by simpa [Level.eval] using h0)
      · have hle := Level.leq_sound (hleq (by simpa using hnp)) ψ
        exact univ_mono hle _ (hmem ρ hρ)
    · rw [← hFsEq]
      exact fieldsValid_of_frame rfl hΓlen hC.okΓ 0 (Nat.zero_le _) ρ hρ'
    · intro hnp
      rw [← hFsEq]
      refine fieldsBound_of_frame rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ
      obtain ⟨u, -, hleq, -, hmem⟩ := hrow j hj
      have hle := Level.leq_sound (hleq hnp) ψ
      exact univ_mono hle _ (hmem ρ hρ)
    · intro hp hl
      rw [← hFsEq]
      refine fieldsBound_of_frame rfl hΓlen ?_ 0 (Nat.zero_le _) ρ hρ'
      intro j hj ρ hρ
      obtain ⟨u, -, -, hz, hmem⟩ := hrow j hj
      have h0 := Level.isEquiv_sound (beq_iff_eq.mp (hz hp hl)) ψ
      have := hmem ρ hρ
      rwa [h0] at this
  exact ⟨fun ψ => (hframes ψ).1, fun ψ => (hframes ψ).2⟩

end Setlec.SetP
