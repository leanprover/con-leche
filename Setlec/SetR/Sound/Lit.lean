import Setlec.SetR.Sound.Motives
import Setlec.Verify.Denote.SubstAlgebra

/-!
# Soundness cases — the literal rules (task #148, T4, batch f1)

I4/I5 (literal inference), R8 (`Nat.succ` packing) and R7/R16 (the
string-literal constructor step) — the `Model/NatLit.lean` /
`Model/StrLit.lean` re-hangs.

The membership route is **`mem_type`-based, not pin-based**: the
literal guards check stored *type shapes*, not basis pinning, so a
numeral's membership in the stored `Nat`'s interpretation is the
zero's `mem_type` plus `app_mem_piC` along the succ's checked
`Nat → Nat` shape — uniform over pinned and user-stored blocks alike.
The string chain applies the same walk (`TeleFitV.appN`/`appN_annot`
over each support constant's denoted checked type) along the
character list.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

section Cases

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-! ### The `Nat` facts -/

/-- The three `Nat` heads' key facts, extracted once: the zero's
membership and the succ's `piC`-membership over the stored `Nat`'s
interpretation. -/
theorem natHeads_facts (henv : EnvSHyp V env cval φ)
    (hs : natLitSupported env = true) (ρ : Nat → V) :
    interp V ρ (cval natZeroName (Level.substFn φ [] []))
      ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) ∧
    interp V ρ (cval natSuccName (Level.substFn φ [] []))
      ∈ˢ piC (interp V ρ (cval natName (Level.substFn φ [] [])))
          (fun _ => interp V ρ (cval natName (Level.substFn φ [] []))) := by
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN, hlpZ,
    hlpS, hTN, hTZ, nm, mb, hTS⟩ := natLitSupported_inv hs
  have hK : ∀ D : Nat, denote cval env φ D (.const natName []) =
      some (cval natName (Level.substFn φ [] [])) := by
    intro D
    rw [denote_const, hfN]
    simp [ConstantInfo.toConstantVal, hlpN]
  constructor
  · have h := henv.mem_type natZeroName _ hfZ []
      (by simp [ConstantInfo.toConstantVal, hlpZ])
      (cval natName (Level.substFn φ [] []))
      (by
        show denoteClosed cval env φ
          (cv0.type.instantiateLevelParams cv0.levelParams []) = _
        rw [hlpZ, hTZ]
        exact hK 0) ρ
    simpa [ConstantInfo.toConstantVal, hlpZ] using h.1
  · have h := henv.mem_type natSuccName _ hfS []
      (by simp [ConstantInfo.toConstantVal, hlpS])
      (.pi (cval natName (Level.substFn φ [] []))
        (cval natName (Level.substFn φ [] [])))
      (by
        show denoteClosed cval env φ
          (cv1.type.instantiateLevelParams cv1.levelParams []) = _
        rw [hlpS, hTS]
        show denote cval env φ 0
          (.forallE nm (.const natName []) (.const natName []) _) = _
        rw [denote_forallE, hK 0]
        simp only [Expr.instantiate1, hK 1]) ρ
    have hmem := h.1
    simp only [ConstantInfo.toConstantVal, hlpS, interp_pi] at hmem
    have hfibre : (fun x => interp V (cons V x ρ)
        (cval natName (Level.substFn φ [] [])))
        = fun _ => interp V ρ (cval natName (Level.substFn φ [] [])) := by
      funext x
      exact interp_closed V (henv.cval_closed _ _) _ ρ
    rwa [hfibre] at hmem

/-- Numerals are truthful and inhabit the stored `Nat`'s
interpretation. -/
theorem natLit_facts (henv : EnvSHyp V env cval φ)
    (hs : natLitSupported env = true) (ρ : Nat → V) :
    ∀ n : Nat,
      AnnotOkV V ρ (natLitV cval φ n) ∧
      interp V ρ (natLitV cval φ n)
        ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) := by
  obtain ⟨hz, hsucc⟩ := natHeads_facts henv hs ρ
  intro n
  induction n with
  | zero => exact ⟨henv.annot_okV _ _ ρ, hz⟩
  | succ n ih =>
    obtain ⟨ihA, ihm⟩ := ih
    constructor
    · show AnnotOkV V ρ (.app (succV cval φ) (natLitV cval φ n))
      rw [AnnotOkV_app]
      exact ⟨henv.annot_okV _ _ ρ, ihA, _, _, hsucc, ihm⟩
    · show interp V ρ (.app (succV cval φ) (natLitV cval φ n)) ∈ˢ _
      rw [interp_app]
      exact app_mem_piC hsucc ihm

/-- I4: `Nat` literals. -/
theorem sndInfLitNat (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {n : Nat}
    (hs : natLitSupported env = true) :
    InfS V Δ (natLitV cval φ n)
      (cval natName (Level.substFn φ [] [])) :=
  fun ρ _ => natLit_facts henv hs ρ n

/-- R8: `Nat.succ` literal packing. -/
theorem sndRedNatSucc (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {va : VExpr} {n : Nat}
    (hs : natLitSupported env = true)
    (_ : Red μ env cval φ Δ va (natLitV cval φ n))
    (ih : RedS V Δ va (natLitV cval φ n)) :
    RedS V Δ (.app (succV cval φ) va) (natLitV cval φ (n + 1)) := by
  intro ρ hΔ
  refine ⟨?_, fun _ => (natLit_facts henv hs ρ (n + 1)).1⟩
  show SetTheory.app _ _
    = interp V ρ (.app (succV cval φ) (natLitV cval φ n))
  rw [interp_app, (ih ρ hΔ).1]

/-! ### The `String` facts -/

/-- Everything the string chain needs, in one bundle: the
truthfulness and the stored-`String` membership of the string-literal
term, by one walk (`TeleFitV.appN`/`appN_annot`) along the support
constants' denoted checked types. -/
theorem strLit_facts (henv : EnvSHyp V env cval φ)
    (hg : strLitSupported env = true) (ρ : Nat → V) (s : String) :
    AnnotOkV V ρ (strLitT cval env φ s) ∧
    interp V ρ (strLitT cval env φ s)
      ∈ˢ interp V ρ (cval stringName (Level.substFn φ [] [])) := by
  obtain ⟨hs, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO,
    hfL, hfN, hfC, hfH, hfF, hlpS, hlpO, hlpL, hlpN, hlpC, hlpH, hlpF,
    hTS, hTH, ⟨nmO, mbO, hTO⟩, ⟨nmL, mbL, hTL⟩, ⟨nmN, mbN, hTN⟩,
    ⟨nm1, nm2, nm3, mb1, mb2, mb3, hTC⟩, ⟨nmF, mbF, hTF⟩⟩ :=
    strLitSupported_inv hg
  have hlpAtN : levelParamsAt env listNilName
      = ciN.toConstantVal.levelParams := by rw [levelParamsAt, hfN]
  have hlpAtC : levelParamsAt env listConsName
      = ciC.toConstantVal.levelParams := by rw [levelParamsAt, hfC]
  -- shared const-denote facts
  have hKL : ∀ D : Nat, denote cval env φ D (.const listName [.zero]) =
      some (cval listName
        (Level.substFn φ ciL.toConstantVal.levelParams [.zero])) := by
    intro D
    rw [denote_const, hfL]
    simp [hlpL]
  have hKH : ∀ D : Nat, denote cval env φ D (.const charName []) =
      some (cval charName (Level.substFn φ [] [])) := by
    intro D
    rw [denote_const, hfH]
    simp [hlpH]
  -- closedness of the two type heads
  have hKLc : VExpr.Closed
      (cval listName (Level.substFn φ ciL.toConstantVal.levelParams
        [.zero])) := henv.cval_closed _ _
  have hKHc : VExpr.Closed (cval charName (Level.substFn φ [] [])) :=
    henv.cval_closed _ _
  -- `Char`'s interpretation is a type in `univ 1`
  have hCharU : interp V ρ (cval charName (Level.substFn φ [] []))
      ∈ˢ (univ 1 : V) := by
    have h := henv.mem_type charName _ hfH []
      (by simp [hlpH])
      (.sort 1)
      (by
        show denoteClosed cval env φ
          (ciH.toConstantVal.type.instantiateLevelParams
            ciH.toConstantVal.levelParams []) = _
        rw [hlpH, hTH]
        show denote cval env φ 0 (.sort (.succ .zero)) = _
        rw [denote_sort]
        simp [Level.eval]) ρ
    simpa [hlpH] using h.1
  -- `List`'s membership, for the tower domains' packages
  have hListMem : interp V ρ
        (cval listName (Level.substFn φ ciL.toConstantVal.levelParams
          [.zero]))
      ∈ˢ piC (univ 1 : V) (fun _ => (univ 1 : V)) := by
    have h := henv.mem_type listName _ hfL [.zero]
      (by simp [hlpL])
      (.pi (.sort 1) (.sort 1))
      (by
        show denoteClosed cval env φ
          (ciL.toConstantVal.type.instantiateLevelParams
            ciL.toConstantVal.levelParams [.zero]) = _
        rw [hlpL, hTL]
        simp only [Expr.instantiateLevelParams, Level.subst,
          Level.subst.go]
        show denote cval env φ 0
          (.forallE nmL (.sort (.succ .zero)) (.sort (.succ .zero)) _)
          = _
        rw [denote_forallE, denote_sort]
        simp +decide [Expr.instantiate1, denote_sort, Level.eval]) ρ
    have hmem := h.1
    rw [interp_pi, interp_sort] at hmem
    simpa using hmem
  -- truthfulness of the recurring `.app ⟦List⟧ e` domains
  have hAppDomOk : ∀ (ρ' : Nat → V) (e : VExpr),
      interp V ρ' e ∈ˢ (univ 1 : V) → AnnotOkV V ρ' e →
      AnnotOkV V ρ'
        (.app (cval listName (Level.substFn φ
          ciL.toConstantVal.levelParams [.zero])) e) := by
    intro ρ' e hmem hok
    rw [AnnotOkV_app]
    refine ⟨henv.annot_okV _ _ ρ', hok, univ 1, fun _ => univ 1, ?_, hmem⟩
    rw [interp_closed V hKLc ρ' ρ]
    exact hListMem
  -- the nil node's head membership, at the term's own spelling
  have hnilMem : interp V ρ (cval listNilName
        (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
      ∈ˢ interp V ρ (.pi (.sort 1)
          (.app (cval listName (Level.substFn φ
            ciL.toConstantVal.levelParams [.zero])) (.bvar 0))) := by
    rw [hlpAtN]
    refine (henv.mem_type listNilName _ hfN [.zero] (by simp [hlpN]) _
      ?_ ρ).1
    rw [hlpN, hTN]
    simp only [Expr.instantiateLevelParams, Level.subst,
      Level.subst.go, List.map_cons, List.map_nil]
    show denote cval env φ 0
      (.forallE nmN (.sort (.succ .zero))
        (.app (.const listName [.zero]) (.bvar 0)) _) = _
    rw [denote_forallE, denote_sort]
    simp +decide only [Expr.instantiate1, denote_app, hKL 1,
      denote_fvar, Level.eval, if_true, Nat.reduceSub]
  have hnilFit : TeleFitV V ρ
      (.pi (.sort 1)
        (.app (cval listName (Level.substFn φ
          ciL.toConstantVal.levelParams [.zero])) (.bvar 0)))
      [cval charName (Level.substFn φ [] [])]
      (.app (cval listName (Level.substFn φ
          ciL.toConstantVal.levelParams [.zero]))
        (cval charName (Level.substFn φ [] []))) := by
    refine TeleFitV.cons (by rw [interp_sort]; exact hCharU) ?_
    have h : (VExpr.app (cval listName (Level.substFn φ
        ciL.toConstantVal.levelParams [.zero])) (.bvar 0)).inst
          (cval charName (Level.substFn φ [] []))
        = .app (cval listName (Level.substFn φ
            ciL.toConstantVal.levelParams [.zero]))
          (cval charName (Level.substFn φ [] [])) := by
      simp [VExpr.inst_app, VExpr.inst_bvar,
        VExpr.inst_eq_self_of_closed hKLc, VExpr.liftN_zero]
    rw [h]
    exact TeleFitV.nil
  have hnilOk : AnnotOkV V ρ
      (.pi (.sort 1)
        (.app (cval listName (Level.substFn φ
          ciL.toConstantVal.levelParams [.zero])) (.bvar 0))) := by
    rw [AnnotOkV_pi]
    refine ⟨by simp, fun x hx => ?_⟩
    rw [interp_sort] at hx
    refine hAppDomOk _ _ ?_ (by simp)
    rw [interp_bvar, cons_zero]
    exact hx
  have hnilA : AnnotOkV V ρ
      (.app (cval listNilName
        (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
        (cval charName (Level.substFn φ [] []))) := by
    refine TeleFitV.appN_annot V hnilFit hnilOk ?_ hnilMem
      (henv.annot_okV _ _ ρ)
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact henv.annot_okV _ _ ρ
  have hnilm := TeleFitV.appN V hnilFit hnilMem
  -- the cons head
  have hconsMem : interp V ρ (cval listConsName
        (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
      ∈ˢ interp V ρ (.pi (.sort 1) (.pi (.bvar 0)
          (.pi (.app (cval listName (Level.substFn φ
              ciL.toConstantVal.levelParams [.zero])) (.bvar 1))
            (.app (cval listName (Level.substFn φ
              ciL.toConstantVal.levelParams [.zero])) (.bvar 2))))) := by
    rw [hlpAtC]
    refine (henv.mem_type listConsName _ hfC [.zero] (by simp [hlpC]) _
      ?_ ρ).1
    rw [hlpC, hTC]
    simp only [Expr.instantiateLevelParams, Level.subst,
      Level.subst.go, List.map_cons, List.map_nil]
    show denote cval env φ 0
      (.forallE nm1 (.sort (.succ .zero))
        (.forallE nm2 (.bvar 0)
          (.forallE nm3 (.app (.const listName [.zero]) (.bvar 1))
            (.app (.const listName [.zero]) (.bvar 2)) _) _) _)
      = _
    rw [denote_forallE, denote_sort]
    simp +decide only [Expr.instantiate1, denote_forallE, denote_fvar,
      denote_app, hKL 2, hKL 3, Level.eval, if_true, if_false,
      Nat.reduceSub, Nat.reduceAdd]
  have hconsOk : AnnotOkV V ρ
      (.pi (.sort 1) (.pi (.bvar 0)
        (.pi (.app (cval listName (Level.substFn φ
            ciL.toConstantVal.levelParams [.zero])) (.bvar 1))
          (.app (cval listName (Level.substFn φ
            ciL.toConstantVal.levelParams [.zero])) (.bvar 2))))) := by
    rw [AnnotOkV_pi]
    refine ⟨by simp, fun x hx => ?_⟩
    rw [interp_sort] at hx
    rw [AnnotOkV_pi]
    refine ⟨by simp, fun y _hy => ?_⟩
    rw [AnnotOkV_pi]
    refine ⟨?_, fun z _hz => ?_⟩
    · refine hAppDomOk _ _ ?_ (by simp)
      simpa using hx
    · refine hAppDomOk _ _ ?_ (by simp)
      simpa using hx
  -- the `Char.ofNat` head
  have hofMem : interp V ρ (cval charOfNatName (Level.substFn φ [] []))
      ∈ˢ interp V ρ (.pi (cval natName (Level.substFn φ [] []))
          (cval charName (Level.substFn φ [] []))) := by
    have h := (henv.mem_type charOfNatName _ hfF [] (by simp [hlpF])
      (.pi (cval natName (Level.substFn φ [] []))
        (cval charName (Level.substFn φ [] []))) ?_ ρ).1
    · rwa [hlpF] at h
    rw [hlpF, hTF]
    show denote cval env φ 0
      (.forallE nmF (.const natName []) (.const charName []) _) = _
    obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hfNat, -, -, hlpNat, -⟩ :=
      natLitSupported_inv hs
    have hKn : denote cval env φ 0 (.const natName []) =
        some (cval natName (Level.substFn φ [] [])) := by
      rw [denote_const, hfNat]
      simp [ConstantInfo.toConstantVal, hlpNat]
    rw [denote_forallE, hKn]
    simp only [Expr.instantiate1, hKH 1]
  -- one character element
  have helem : ∀ c : Char,
      AnnotOkV V ρ (.app (cval charOfNatName (Level.substFn φ [] []))
        (natLitV cval φ c.toNat)) ∧
      interp V ρ (.app (cval charOfNatName (Level.substFn φ [] []))
        (natLitV cval φ c.toNat))
        ∈ˢ interp V ρ (cval charName (Level.substFn φ [] [])) := by
    intro c
    obtain ⟨hnA, hnm⟩ := natLit_facts henv hs ρ c.toNat
    have hofFit : TeleFitV V ρ
        (.pi (cval natName (Level.substFn φ [] []))
          (cval charName (Level.substFn φ [] [])))
        [natLitV cval φ c.toNat]
        (cval charName (Level.substFn φ [] [])) := by
      refine TeleFitV.cons hnm ?_
      rw [VExpr.inst_eq_self_of_closed hKHc]
      exact TeleFitV.nil
    have hofOk : AnnotOkV V ρ
        (.pi (cval natName (Level.substFn φ [] []))
          (cval charName (Level.substFn φ [] []))) := by
      rw [AnnotOkV_pi]
      exact ⟨henv.annot_okV _ _ ρ,
        fun x _ => henv.annot_okV _ _ (cons V x ρ)⟩
    refine ⟨TeleFitV.appN_annot V hofFit hofOk ?_ hofMem
        (henv.annot_okV _ _ ρ),
      TeleFitV.appN V hofFit hofMem⟩
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact hnA
  -- the character-list walk
  have hchain : ∀ cs : List Char,
      AnnotOkV V ρ (charListT
        (.app (cval listNilName
          (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
          (cval charName (Level.substFn φ [] [])))
        (.app (cval listConsName
          (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
          (cval charName (Level.substFn φ [] [])))
        (cval charOfNatName (Level.substFn φ [] []))
        (cval natZeroName (Level.substFn φ [] []))
        (cval natSuccName (Level.substFn φ [] [])) cs) ∧
      interp V ρ (charListT
        (.app (cval listNilName
          (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
          (cval charName (Level.substFn φ [] [])))
        (.app (cval listConsName
          (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
          (cval charName (Level.substFn φ [] [])))
        (cval charOfNatName (Level.substFn φ [] []))
        (cval natZeroName (Level.substFn φ [] []))
        (cval natSuccName (Level.substFn φ [] [])) cs)
        ∈ˢ interp V ρ
          (.app (cval listName (Level.substFn φ
              ciL.toConstantVal.levelParams [.zero]))
            (cval charName (Level.substFn φ [] []))) := by
    intro cs
    induction cs with
    | nil => exact ⟨hnilA, hnilm⟩
    | cons c cs ih =>
      obtain ⟨ihA, ihm⟩ := ih
      obtain ⟨heA, hem⟩ := helem c
      have hfit : TeleFitV V ρ
          (.pi (.sort 1) (.pi (.bvar 0)
            (.pi (.app (cval listName (Level.substFn φ
                ciL.toConstantVal.levelParams [.zero])) (.bvar 1))
              (.app (cval listName (Level.substFn φ
                ciL.toConstantVal.levelParams [.zero])) (.bvar 2)))))
          [cval charName (Level.substFn φ [] []),
           .app (cval charOfNatName (Level.substFn φ [] []))
             (natLitV cval φ c.toNat),
           charListT
             (.app (cval listNilName (Level.substFn φ
               (levelParamsAt env listNilName) [.zero]))
               (cval charName (Level.substFn φ [] [])))
             (.app (cval listConsName (Level.substFn φ
               (levelParamsAt env listConsName) [.zero]))
               (cval charName (Level.substFn φ [] [])))
             (cval charOfNatName (Level.substFn φ [] []))
             (cval natZeroName (Level.substFn φ [] []))
             (cval natSuccName (Level.substFn φ [] [])) cs]
          (.app (cval listName (Level.substFn φ
              ciL.toConstantVal.levelParams [.zero]))
            (cval charName (Level.substFn φ [] []))) := by
        refine TeleFitV.cons (by rw [interp_sort]; exact hCharU) ?_
        have h1 : (VExpr.pi (.bvar 0)
            (.pi (.app (cval listName (Level.substFn φ
                ciL.toConstantVal.levelParams [.zero])) (.bvar 1))
              (.app (cval listName (Level.substFn φ
                ciL.toConstantVal.levelParams [.zero])) (.bvar 2)))).inst
              (cval charName (Level.substFn φ [] []))
            = .pi (cval charName (Level.substFn φ [] []))
                (.pi (.app (cval listName (Level.substFn φ
                    ciL.toConstantVal.levelParams [.zero]))
                  (cval charName (Level.substFn φ [] [])))
                  (.app (cval listName (Level.substFn φ
                    ciL.toConstantVal.levelParams [.zero]))
                  (cval charName (Level.substFn φ [] [])))) := by
          simp +decide [VExpr.inst_pi, VExpr.inst_app, VExpr.inst_bvar,
            VExpr.inst_eq_self_of_closed hKLc,
            VExpr.liftN_eq_self_of_closed hKHc]
        rw [h1]
        refine TeleFitV.cons hem ?_
        rw [VExpr.inst_eq_self_of_closed
          (show VExpr.Closed (VExpr.pi
            (.app (cval listName (Level.substFn φ
              ciL.toConstantVal.levelParams [.zero]))
              (cval charName (Level.substFn φ [] [])))
            (.app (cval listName (Level.substFn φ
              ciL.toConstantVal.levelParams [.zero]))
              (cval charName (Level.substFn φ [] []))))
            from ⟨⟨hKLc, hKHc⟩,
              VExpr.bvarsBelow.mono (Nat.zero_le 1) hKLc,
              VExpr.bvarsBelow.mono (Nat.zero_le 1) hKHc⟩)]
        refine TeleFitV.cons (by rw [interp_app]; exact ihm) ?_
        rw [VExpr.inst_eq_self_of_closed
          (show VExpr.Closed (VExpr.app (cval listName (Level.substFn φ
              ciL.toConstantVal.levelParams [.zero]))
              (cval charName (Level.substFn φ [] [])))
            from ⟨hKLc, hKHc⟩)]
        exact TeleFitV.nil
      refine ⟨?_, TeleFitV.appN V hfit hconsMem⟩
      refine TeleFitV.appN_annot V hfit hconsOk ?_ hconsMem
        (henv.annot_okV _ _ ρ)
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact henv.annot_okV _ _ ρ
      · exact heA
      · exact ihA
  -- the outer `String.ofList` application
  have hOFMem : interp V ρ
        (cval stringOfListName (Level.substFn φ [] []))
      ∈ˢ interp V ρ (.pi
          (.app (cval listName (Level.substFn φ
              ciL.toConstantVal.levelParams [.zero]))
            (cval charName (Level.substFn φ [] [])))
          (cval stringName (Level.substFn φ [] []))) := by
    have h := (henv.mem_type stringOfListName _ hfO [] (by simp [hlpO])
      (.pi (.app (cval listName (Level.substFn φ
            ciL.toConstantVal.levelParams [.zero]))
          (cval charName (Level.substFn φ [] [])))
        (cval stringName (Level.substFn φ [] []))) ?_ ρ).1
    · rwa [hlpO] at h
    rw [hlpO, hTO]
    show denote cval env φ 0
      (.forallE nmO
        (.app (.const listName [.zero]) (.const charName []))
        (.const stringName []) _) = _
    rw [denote_forallE, denote_app, hKL 0, hKH 0]
    have hKS : denote cval env φ 1 (.const stringName []) =
        some (cval stringName (Level.substFn φ [] [])) := by
      rw [denote_const, hfS]
      simp [hlpS]
    simp only [Expr.instantiate1, hKS]
  obtain ⟨hclA, hclm⟩ := hchain s.toList
  have hOFFit : TeleFitV V ρ
      (.pi (.app (cval listName (Level.substFn φ
            ciL.toConstantVal.levelParams [.zero]))
          (cval charName (Level.substFn φ [] [])))
        (cval stringName (Level.substFn φ [] [])))
      [charListT
        (.app (cval listNilName
          (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
          (cval charName (Level.substFn φ [] [])))
        (.app (cval listConsName
          (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
          (cval charName (Level.substFn φ [] [])))
        (cval charOfNatName (Level.substFn φ [] []))
        (cval natZeroName (Level.substFn φ [] []))
        (cval natSuccName (Level.substFn φ [] [])) s.toList]
      (cval stringName (Level.substFn φ [] [])) := by
    refine TeleFitV.cons hclm ?_
    rw [VExpr.inst_eq_self_of_closed (henv.cval_closed _ _)]
    exact TeleFitV.nil
  have hOFOk : AnnotOkV V ρ
      (.pi (.app (cval listName (Level.substFn φ
            ciL.toConstantVal.levelParams [.zero]))
          (cval charName (Level.substFn φ [] [])))
        (cval stringName (Level.substFn φ [] []))) := by
    rw [AnnotOkV_pi]
    refine ⟨?_, fun x _ => henv.annot_okV _ _ (cons V x ρ)⟩
    exact hAppDomOk _ _ hCharU (henv.annot_okV _ _ ρ)
  constructor
  · show AnnotOkV V ρ (.app (cval stringOfListName _) _)
    refine TeleFitV.appN_annot V hOFFit hOFOk ?_ hOFMem
      (henv.annot_okV _ _ ρ)
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact hclA
  · show interp V ρ (.app (cval stringOfListName _) _) ∈ˢ _
    exact TeleFitV.appN V hOFFit hOFMem

/-- I5: `String` literals. -/
theorem sndInfLitStr (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {s : String}
    (hg : strLitSupported env = true) :
    InfS V Δ (strLitT cval env φ s)
      (cval stringName (Level.substFn φ [] [])) :=
  fun ρ _ => strLit_facts henv hg ρ s

/-! ### R7/R16: the string-literal constructor step -/

/-- A string literal's constructor form denotes to the literal's own
term (the transpose of the TT lane's `denote_strLitToConstructor`,
over the guard's shape facts). -/
theorem denoteClosed_strLitToConstructor
    (hg : strLitSupported env = true) (s : String) :
    denoteClosed cval env φ (strLitToConstructor s)
      = some (strLitT cval env φ s) := by
  obtain ⟨hs, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC, hfS, hfO,
    hfL, hfN, hfC, hfH, hfF, hlpS, hlpO, hlpL, hlpN, hlpC, hlpH, hlpF,
    -, -, -, -, -, -, -⟩ := strLitSupported_inv hg
  have hlpAtN : levelParamsAt env listNilName
      = ciN.toConstantVal.levelParams := by rw [levelParamsAt, hfN]
  have hlpAtC : levelParamsAt env listConsName
      = ciC.toConstantVal.levelParams := by rw [levelParamsAt, hfC]
  have hKH : denote cval env φ 0 (.const charName []) =
      some (cval charName (Level.substFn φ [] [])) := by
    rw [denote_const, hfH]
    simp [hlpH]
  have hlist : ∀ cs : List Char,
      denote cval env φ 0
        (cs.foldr
          (init := .app (.const listNilName [.zero]) (.const charName []))
          fun c e =>
            .app (.app (.app (.const listConsName [.zero])
              (.const charName []))
              (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e)
        = some (charListT
          (.app (cval listNilName
            (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
            (cval charName (Level.substFn φ [] [])))
          (.app (cval listConsName
            (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
            (cval charName (Level.substFn φ [] [])))
          (cval charOfNatName (Level.substFn φ [] []))
          (cval natZeroName (Level.substFn φ [] []))
          (cval natSuccName (Level.substFn φ [] [])) cs) := by
    intro cs
    induction cs with
    | nil =>
      show denote cval env φ 0
        (.app (.const listNilName [.zero]) (.const charName [])) = _
      rw [denote_app, denote_const, hfN, hKH]
      simp [hlpN, hlpAtN, charListT]
    | cons c cs ih =>
      show denote cval env φ 0
        (.app (.app (.app (.const listConsName [.zero])
          (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat))))
          (cs.foldr _ _)) = _
      rw [denote_app, denote_app, denote_app, denote_const, hfC, hKH,
        denote_app, denote_const, hfF, denote_natLit, if_pos hs, ih]
      simp [hlpC, hlpF, hlpAtC, charListT]
  show denote cval env φ 0
    (.app (.const stringOfListName []) _) = _
  rw [denote_app, denote_const, hfO, hlist s.toList]
  simp [hlpO, strLitT]

/-- R7/R16: a string literal steps to (the reduction of) its denoted
constructor form. -/
theorem sndRedStrLitCtor {Δ : List VExpr} {sarg : String} {SC P : VExpr}
    (hg : strLitSupported env = true)
    (h2 : denoteClosed cval env φ (strLitToConstructor sarg) = some SC)
    (_ : VExpr.Closed SC)
    (_ : Red μ env cval φ Δ SC P)
    (ih : RedS V Δ SC P) :
    RedS V Δ (strLitT cval env φ sarg) P := by
  have hSC : SC = strLitT cval env φ sarg := by
    rw [denoteClosed_strLitToConstructor hg] at h2
    exact (Option.some.inj h2).symm
  subst hSC
  exact ih

end Cases

end Setlec.SetR
