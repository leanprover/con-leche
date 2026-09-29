module

import ConLeche.Model.Inductives.DeclBlock
public import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.DeclNative

public section

/-!
# A class guard fits the block's PARAMETERS

`tgtClsG` guards recursor class `c` by the prefix fit — and, at a MEMBER
major, by the parameters' fit too.  At an OUTSIDE major the parameters'
fit is not in the guard; it FOLLOWS from the prefix fit, by the kernel's
K6 check in `targetRecTy`: the recursor's first `nP` binder domains are
compared binder by binder with the MAJOR's former's parameter domains —
an outside major's former being the block's FIRST (`cvTas.head?`).  The
hop is `blockRecParams_run`'s forward direction, stated here at any
former `t` of the block (`recParams_fit_former`), and the members'
parameter agreement (`paramsIff`) at `t` closes it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo openPisAtFvars
  BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The recursor's parameter domains fit the block's, against ANY
former `t` of the block** its first `nP` binder domains were checked
defeq to — `blockRecParams_run`'s forward direction, with the former
(and the recursor type's opening) as data rather than a `RecTyEntry`. -/
theorem recParams_fit_former (hμ : μ.verifiedChecks = true) {envC : Env} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {d : BlockData V} (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {fvs : List Expr} {concl : Expr}
    (hop : openPisAtFvars (p.toBlockShape.majorIdxAt c + 1) r.1.type 0 = some (fvs, concl))
    (hnPle : p.nP ≤ p.toBlockShape.majorIdxAt c)
    {t : Nat} {cvTP : ConstantVal} (hcvT : cvTas[t]? = some cvTP)
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars p.nP cvTP.type 0 = some (tfvs, trest))
    (hdeq : ∀ l, l < p.nP →
      ConLeche.isDefEqCore μ envC F p.nP ((tfvs.map Expr.fvarTypeD).getD l default)
        (((fvs.take p.nP).map Expr.fvarTypeD).getD l default) = .ok true)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hfit : SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).take d.nP) xs) :
    SpineFit ρ (d.params ψ) xs := by
  obtain ⟨hnPq, hkq, hlenCv, hcvF, -, -, hparIff⟩ := hmr
  have hmemk : t < d.k := by
    rw [← hlenCv]; exact (List.getElem?_eq_some_iff.mp hcvT).1
  obtain ⟨fvsL, conclL, hopL, hread, hmk, hlenRds, -, hbind, -, hwdTy⟩ :=
    recStage_tyPis hμ mpC h hr ψ
  have hfvE : fvsL = fvs := congrArg Prod.fst (Option.some.inj (hopL.symm.trans hop))
  rw [hfvE] at hbind
  obtain ⟨-, -, -, hfvT, hbndT, hFD⟩ := hcvF _ _ hcvT
  have hppsLen : (d.ppsM t ψ).length = d.nP + d.nIdxAt t := hFD.len ψ
  -- the two openings, at the block's parameter count
  obtain ⟨hwA, hbA⟩ := recStage_tyClosed h hr
  obtain ⟨fvsA, fvs', oA, hopA, -, hfvsplit⟩ :=
    openPisAtFvars_split (e := r.1.type) (d := 0) p.nP
      (by rw [show p.nP + (p.toBlockShape.majorIdxAt c + 1 - p.nP)
            = p.toBlockShape.majorIdxAt c + 1 from by omega]
          exact hop)
  have hlenA : fvsA.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hopA
  have hfvsA : fvs.take p.nP = fvsA := by
    rw [hfvsplit, List.take_append_of_le_length (Nat.le_of_eq hlenA.symm),
      List.take_of_length_le (Nat.le_of_eq hlenA)]
  have hdA : ∀ (i : Nat) (x : Expr), fvsA[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x)
        = some ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take p.nP).map
            (·.2.2)).getD i default) := by
    intro i x hx
    have hi : i < p.nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [hlenA] at this; exact this
    have hx' : fvs[i]? = some x := by
      rw [← hfvsA, List.getElem?_take, if_pos hi] at hx
      exact hx
    obtain ⟨pd, hpd, -, hreadD⟩ := hbind i x hx'
    rw [hreadD, List.map_take, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi, List.getElem?_map, hpd]
    rfl
  have hokA : ∀ i, i < p.nP → ∀ (ρ' : Nat → V) (ys : List V),
      SpineFit ρ' ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take
        p.nP).map (·.2.2)).take i) ys →
      WellDenotedV V (consList ys ρ')
        ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take p.nP).map
          (·.2.2)).getD i default) :=
    fun i hi ρ' ys hys => prefixDoms_graded_of_tower (V := V)
      (cc := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c)
      (by rw [hlenRds]; omega) (fun ρ'' => by rw [← hmk]; exact hwdTy ρ'') hi hys
  -- the former's side
  obtain ⟨ppsT, bT, hstT, -, -, hbindT⟩ :=
    denoteMeta_openPis (acval := mpC.base2.acval) (env := envC) (φ := ψ) p.nP hopT (hFD.read ψ)
  have hppsT : ppsT = (d.ppsM t ψ).take p.nP := by
    have := stripPisAV_mkPisAV_take p.nP (d.ppsM t ψ)
      (.sort (d.resSort.eval ψ)) (by rw [hppsLen, hnPq]; omega)
    rw [this] at hstT
    exact congrArg Prod.fst (Option.some.inj hstT.symm)
  have hdB : ∀ (i : Nat) (x : Expr), tfvs[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x)
        = some ((((d.ppsM t ψ).take d.nP).map (·.2.2)).getD i default) := by
    intro i x hx
    obtain ⟨pd, hpd, -, hreadD⟩ := hbindT i x hx
    rw [Nat.zero_add] at hreadD
    rw [hreadD, hnPq, ← hppsT, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]
    rfl
  have hokB : ∀ i, i < p.nP → ∀ (ρ' : Nat → V) (ys : List V),
      SpineFit ρ' ((((d.ppsM t ψ).take d.nP).map (·.2.2)).take i) ys →
      WellDenotedV V (consList ys ρ') ((((d.ppsM t ψ).take d.nP).map (·.2.2)).getD i
        default) := by
    intro i hi ρ' ys hys
    rw [hnPq] at hys ⊢
    exact prefixDoms_graded_of_tower (V := V) (cc := .sort (d.resSort.eval ψ))
      (by rw [hppsLen, hnPq]; omega) (fun ρ'' => hFD.okTy ψ ρ'') hi hys
  have hlenPD : (d.params ψ).length = d.nP := by
    obtain ⟨cvT0, hcvT0⟩ : ∃ cvT0, cvTas[0]? = some cvT0 :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; omega)⟩
    obtain ⟨-, -, -, -, -, hFD0⟩ := hcvF _ _ hcvT0
    rw [BlockData.params, List.length_map, List.length_take, hFD0.len ψ]; omega
  have hlenT : (((d.ppsM t ψ).take d.nP).map (·.2.2)).length = d.nP := by
    rw [List.length_map, List.length_take, hppsLen]; omega
  -- the certified hop, then the members' parameter agreement at `t`
  have hfitA : SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take
      p.nP).map (·.2.2)) xs := by
    rw [hnPq] at hfit
    rw [List.map_take]
    exact hfit
  have hfitB := prefixDoms_spineFit (V := V) hμ mpC hopA hopT hwA
    (Expr.WScoped.of_not_hasFvar hfvT) hbA hbndT
    (by rw [List.length_map, List.length_take, hlenRds]; omega)
    (by rw [List.length_map, List.length_take, hppsLen, hnPq]; omega)
    hdA hdB hokA hokB
    (fun l hl => Or.inr (by
      rw [← hfvsA]
      exact hdeq l hl))
    hfitA
  have hsat : Sat V ((((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse) (consList xs ρ) := by
    simpa using sat_of_spineFit (Sat_nil V ρ) hfitB
  exact spineFit_of_sat_consList (by rw [hfitB.length_eq, hlenT, hlenPD])
    ((hparIff _ hmemk ψ _).mp hsat)

end ConLeche.Model
