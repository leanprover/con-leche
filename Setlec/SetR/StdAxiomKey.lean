import Setlec.SetR.Install.Axiom
import Setlec.Verify.StdAxiomPin

/-!
# The standard axioms' inhabitation key (task #148, T5)

`StdAxiomKeyS`, split by name as `stdAxiomOk` splits.

**The witnesses are the layer's own constants.**  `BConst.propext` and
`BConst.choice` exist, with `bval .propext = pt` and
`bval .choice us = choiceV V (lv us 0)`, and `TT/Semantics/ConstOk.lean`
already proves each inhabits *the layer's* type.  So the witness
obligations — closedness, level-invariance, `AnnotOkV` — are
one-liners, and the TT lane's syntactic `Iff.rec`/`Nonempty.rec`
elimination is **not needed**: `HasType` cannot see `bval`, but
membership is semantic, so the checker's hypothesis domain need only
be shown to *force* the conclusion.  `Model/StdAxioms.lean` is the
template, not `TTVerify/StdAxiomKey.lean`.

What is left, per half, is the forcing argument: `⟦Iff a b⟧` inhabited
forces `a = b`, and `⟦Nonempty A⟧` inhabited forces `A` inhabited.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify SetTheory
universe w
variable {V : Type w} [SetTheory V]

/-- The `propext` half of `StdAxiomKeyS`. -/
def PropextKeyS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env : Env} (m : EnvS V env) {cvA : ConstantVal},
    stdAxiomOk env cvA = true → cvA.name = propextName →
    env.find? cvA.name = none →
    ∃ Vf : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (Vf ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) ∧
      (∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t) ∧
      ∀ acval : Name → (Name → Nat) → AVExpr,
        AcvalLink V m.cval acval → AnnotLeaf2 V Vf

/-- The `Classical.choice` half. -/
def ChoiceKeyS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env : Env} (m : EnvS V env) {cvA : ConstantVal},
    stdAxiomOk env cvA = true → cvA.name = choiceName →
    env.find? cvA.name = none →
    ∃ Vf : (Name → Nat) → VExpr, (∀ ψ, VExpr.Closed (Vf ψ)) ∧
      (∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ cvA.levelParams, φ₁ p = φ₂ p) → Vf φ₁ = Vf φ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (Vf ψ)) ∧
      (∀ ψ : Name → Nat, ∃ t,
        denoteClosed m.cval env ψ cvA.type = some t ∧
        ∀ ρ : Nat → V,
          interp V ρ (Vf ψ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t) ∧
      ∀ acval : Name → (Name → Nat) → AVExpr,
        AcvalLink V m.cval acval → AnnotLeaf2 V Vf

/-- The two halves assemble. -/
theorem stdAxiomKeyS_of (hp : PropextKeyS V) (hc : ChoiceKeyS V) :
    StdAxiomKeyS V := by
  intro env m cvA hok hfresh
  by_cases hn : cvA.name = propextName
  · exact hp m hok hn hfresh
  · by_cases hn2 : cvA.name = choiceName
    · exact hc m hok hn2 hfresh
    · exfalso
      unfold stdAxiomOk at hok
      rw [if_neg hn, if_neg hn2] at hok
      exact nomatch hok

/-- `propext`'s pinned type, denoted. -/
theorem denote_propext_typeS {cval : TConstVal} {env : Env}
    {cvI : ConstantVal} {caps : IndCaps}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    (hEq : env.find? eqName = some eqA) (ψ : Name → Nat) :
    denote cval env ψ 0 propextA.type =
      some (.pi (.sort 0) (.pi (.sort 0)
        (.pi (VExpr.mkAppN (cval iffName ψ) [.bvar 1, .bvar 0])
          (VExpr.mkAppN (cval eqName (Level.substFn ψ
              eqA.toConstantVal.levelParams [.succ .zero]))
            [.sort 0, .bvar 2, .bvar 1])))) := by
  have hI : ∀ d, denote cval env ψ d (.const iffName [])
      = some (cval iffName ψ) :=
    fun d => denote_const_nolevelsS hfI hlpI ψ d
  have hQ : ∀ d, denote cval env ψ d (.const eqName [.succ .zero])
      = some (cval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [.succ .zero])) := by
    intro d
    rw [denote_const, hEq]
    exact if_pos rfl
  simp only [iffName, eqName] at hI hQ
  simp [propextA, denote_forallE, denote_sort, Expr.instantiate1,
    denote_app, denote_fvar, VExpr.mkAppN, hI, hQ, Level.eval,
    iffName, eqName]

/-! ## The pinned `Iff` family's memberships

Transposed from `Model/StdAxioms.lean` by `m.val n ψ ↦
interp V ρ (m.cval n ψ)`.  Each is `EnvS.cval_memType` at the stored
constant, its pinned type denoted, and `app_mem_piC`. -/

/-- The stored `Iff` former is `Prop → Prop → Prop`. -/
theorem iffVal_memS {env : Env} (m : EnvS V env)
    {cvI : ConstantVal} {caps : IndCaps}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (htyI : cvI.type.erasePw.eraseNames = iffA.toConstantVal.type.erasePw.eraseNames)
    (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (m.cval iffName ψ)
      ∈ˢ piC (univ 0 : V) fun _ =>
        piC (univ 0 : V) fun _ => (univ 0 : V) := by
  obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfI ψ
  rw [show (ConstantInfo.indInfo cvI caps).toConstantVal = cvI from rfl,
    denoteClosed, denote_pinEq htyI 0] at ht
  simp [iffA, ConstantInfo.toConstantVal, denote_forallE,
    denote_sort, Expr.instantiate1, Level.eval] at ht
  obtain rfl := ht
  exact (hlaw ρ).1

/-- The stored `Iff`, applied to two propositions, is a proposition. -/
theorem iffVal_app₂_memS {env : Env} (m : EnvS V env)
    {cvI : ConstantVal} {caps : IndCaps}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (htyI : cvI.type.erasePw.eraseNames = iffA.toConstantVal.type.erasePw.eraseNames)
    (ψ : Name → Nat) (ρ : Nat → V) {A B : V}
    (hA : A ∈ˢ (univ 0 : V)) (hB : B ∈ˢ (univ 0 : V)) :
    SetTheory.app (SetTheory.app (interp V ρ (m.cval iffName ψ)) A) B
      ∈ˢ (univ 0 : V) :=
  app_mem_piC (app_mem_piC (iffVal_memS m hfI htyI ψ ρ) hA) hB

/-- The stored `Iff.intro`, fully applied, inhabits the family. -/
theorem iffIntroVal_app₄_memS {env : Env} (m : EnvS V env)
    {cvI : ConstantVal} {caps : IndCaps} {cvIi : ConstantVal}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    (hfIi : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (htyIi : cvIi.type.erasePw.eraseNames
      = iffIntroA.toConstantVal.type.erasePw.eraseNames)
    (ψ : Name → Nat) (ρ : Nat → V) {A B mp mpr : V}
    (hA : A ∈ˢ (univ 0 : V)) (hB : B ∈ˢ (univ 0 : V))
    (hmp : mp ∈ˢ piC A (fun _ => B))
    (hmpr : mpr ∈ˢ piC B (fun _ => A)) :
    SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (interp V ρ (m.cval iffIntroName ψ)) A) B) mp) mpr
      ∈ˢ SetTheory.app (SetTheory.app
        (interp V ρ (m.cval iffName ψ)) A) B := by
  obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfIi ψ
  rw [show (ConstantInfo.ctorInfo cvIi 2 2).toConstantVal = cvIi
      from rfl, denoteClosed,
    denote_pinEq htyIi 0] at ht
  have hI : ∀ d, denote m.cval env ψ d (.const iffName [])
      = some (m.cval iffName ψ) :=
    fun d => denote_const_nolevelsS hfI hlpI ψ d
  simp only [iffName] at hI
  simp [iffIntroA, ConstantInfo.toConstantVal, denote_forallE,
    denote_sort, Expr.instantiate1, denote_app, denote_fvar,
    hI, Level.eval] at ht
  obtain rfl := ht
  have h1 := (hlaw ρ).1
  simp only [interp_pi, interp_sort, interp_app, interp_bvar,
    cons_zero, cons_succ,
    interp_closed (V := V) (m.cval_closed _ ψ) _ ρ] at h1
  exact app_mem_piC (app_mem_piC (app_mem_piC (app_mem_piC h1 hA) hB)
    hmp) hmpr

/-- The stored `Iff.rec`, at a `Prop` motive level, is a member of its
interpreted pinned type. -/
theorem iffRecVal_memS {env : Env} (m : EnvS V env)
    {cvI : ConstantVal} {caps : IndCaps} {cvIi : ConstantVal}
    {cvIr : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    (hfIi : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hlpIi : cvIi.levelParams = [])
    (hfIr : env.find? iffRecName = some (.recInfo cvIr mI rP rules))
    (htyIr : cvIr.type.erasePw.eraseNames
      = iffRecA.toConstantVal.type.erasePw.eraseNames)
    {ψ0 : Name → Nat} (h0 : ψ0 uN = 0) (ρ : Nat → V) :
    interp V ρ (m.cval iffRecName ψ0) ∈ˢ
      piC (univ 0) fun A => piC (univ 0) fun B =>
        piC (piC (SetTheory.app (SetTheory.app
            (interp V ρ (m.cval iffName ψ0)) A) B) fun _ => univ 0)
          fun M =>
          piC (piC (piC A fun _ => B) fun mp =>
              piC (piC B fun _ => A) fun mpr =>
                SetTheory.app M (SetTheory.app (SetTheory.app
                  (SetTheory.app (SetTheory.app
                    (interp V ρ (m.cval iffIntroName ψ0)) A) B) mp)
                  mpr))
            fun _ =>
            piC (SetTheory.app (SetTheory.app
              (interp V ρ (m.cval iffName ψ0)) A) B)
              fun t => SetTheory.app M t := by
  obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfIr ψ0
  rw [show (ConstantInfo.recInfo cvIr mI rP rules).toConstantVal = cvIr
      from rfl, denoteClosed,
    denote_pinEq htyIr 0] at ht
  have hI : ∀ d, denote m.cval env ψ0 d (.const iffName [])
      = some (m.cval iffName ψ0) :=
    fun d => denote_const_nolevelsS hfI hlpI ψ0 d
  have hIi : ∀ d, denote m.cval env ψ0 d (.const iffIntroName [])
      = some (m.cval iffIntroName ψ0) :=
    fun d => denote_const_nolevelsS hfIi hlpIi ψ0 d
  have h0' : ψ0 (Name.anonymous.str "u") = 0 := h0
  simp only [iffName, iffIntroName] at hI hIi
  simp [iffRecA, ConstantInfo.toConstantVal, denote_forallE,
    denote_sort, Expr.instantiate1, denote_app, denote_fvar,
    hI, hIi, Level.eval, h0'] at ht
  obtain rfl := ht
  have h1 := (hlaw ρ).1
  simp only [interp_pi, interp_sort, interp_app, interp_bvar,
    cons_zero, cons_succ,
    interp_closed (V := V) (m.cval_closed _ ψ0) _ ρ] at h1
  exact h1

/-- Interpreted `Iff` forces equality of truth values.  The witness is
eliminated at the constantly-`eqv A B` motive, whose minor premise is
`prop_ext` applied to the two stored implications. -/
theorem iff_forces_eqS {env : Env} (m : EnvS V env)
    {cvI : ConstantVal} {caps : IndCaps} {cvIi : ConstantVal}
    {cvIr : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    (hfIi : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hlpIi : cvIi.levelParams = [])
    (htyIi : cvIi.type.erasePw.eraseNames
      = iffIntroA.toConstantVal.type.erasePw.eraseNames)
    (hfIr : env.find? iffRecName = some (.recInfo cvIr mI rP rules))
    (htyIr : cvIr.type.erasePw.eraseNames
      = iffRecA.toConstantVal.type.erasePw.eraseNames)
    (ψ' : Name → Nat) (ρ : Nat → V) {A B w : V}
    (hA : A ∈ˢ (univ 0 : V)) (hB : B ∈ˢ (univ 0 : V))
    (hw : w ∈ˢ SetTheory.app (SetTheory.app
      (interp V ρ (m.cval iffName ψ')) A) B) :
    A = B := by
  -- the parameterless family members do not read the assignment
  have hIval : m.cval iffName (fun _ => 0) = m.cval iffName ψ' :=
    m.val_params _ _ hfI _ _ (by
      rw [show (ConstantInfo.indInfo cvI caps).toConstantVal = cvI
        from rfl, hlpI]
      intro p hp; cases hp)
  have hIival :
      m.cval iffIntroName (fun _ => 0) = m.cval iffIntroName ψ' :=
    m.val_params _ _ hfIi _ _ (by
      rw [show (ConstantInfo.ctorInfo cvIi 2 2).toConstantVal = cvIi
        from rfl, hlpIi]
      intro p hp; cases hp)
  have hvR := iffRecVal_memS m hfI hlpI hfIi hlpIi hfIr htyIr
    (ψ0 := fun _ => 0) rfl ρ
  rw [hIval, hIival] at hvR
  have hIII : ∀ mp' mpr' : V, mp' ∈ˢ piC A (fun _ => B) →
      mpr' ∈ˢ piC B (fun _ => A) →
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (interp V ρ (m.cval iffIntroName ψ')) A) B) mp') mpr'
        ∈ˢ SetTheory.app (SetTheory.app
          (interp V ρ (m.cval iffName ψ')) A) B :=
    fun mp' mpr' hmp' hmpr' =>
      iffIntroVal_app₄_memS m hfI hlpI hfIi htyIi ψ' ρ hA hB hmp' hmpr'
  -- name the two interpreted family members
  obtain ⟨IV, hIVe⟩ : ∃ x, interp V ρ (m.cval iffName ψ') = x :=
    ⟨_, rfl⟩
  obtain ⟨IIV, hIIVe⟩ : ∃ x, interp V ρ (m.cval iffIntroName ψ') = x :=
    ⟨_, rfl⟩
  rw [hIVe, hIIVe] at hvR hIII
  rw [hIVe] at hw
  -- the motive: constantly `eqv A B`
  have hM : lamC (SetTheory.app (SetTheory.app IV A) B)
        (fun _ => eqv A B) ∈ˢ
      piC (SetTheory.app (SetTheory.app IV A) B)
        fun _ => (univ 0 : V) :=
    lamC_mem fun _ _ => eqv_mem_univ A B
  have r3 := app_mem_piC (app_mem_piC (app_mem_piC hvR hA) hB) hM
  have hminor : (pt : V) ∈ˢ
      piC (piC A fun _ => B) fun mp' =>
        piC (piC B fun _ => A) fun mpr' =>
          SetTheory.app (lamC (SetTheory.app (SetTheory.app IV A) B)
              fun _ => eqv A B)
            (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
              IIV A) B) mp') mpr') := by
    refine pt_mem_piC_iff.mpr fun mp' hmp' =>
      pt_mem_piC_iff.mpr fun mpr' hmpr' => ?_
    have hAB : A = B := by
      refine prop_ext hA hB (fun hptA => ?_) (fun hptB => ?_)
      · have h1 := app_mem_piC hmp' hptA
        rwa [mem_univ_zero hB h1] at h1
      · have h1 := app_mem_piC hmpr' hptB
        rwa [mem_univ_zero hA h1] at h1
    rw [app_lamC (hIII mp' mpr' hmp' hmpr')]
    exact hAB ▸ pt_mem_eqv_self A
  have r5 := app_mem_piC (app_mem_piC r3 hminor) hw
  rw [app_lamC hw] at r5
  exact mem_eqv r5

set_option maxHeartbeats 1600000 in
/-- **The `propext` half of the key.**  The witness is the layer's own
`propext` constant, whose value is `pt`; the pinned type's three
`Prop`-level products are `pt`-inhabited because `Iff a b` forces
`a = b`. -/
theorem propextKeyS : PropextKeyS V := by
  intro env m cvA hok hn hfresh
  obtain ⟨hEq, ⟨cvI, caps, hfI, hlpI, htyI⟩, ⟨cvIi, hfIi, hlpIi, htyIi⟩,
    ⟨cvIr, mI, rP, rules, hfIr, hlpIr, htyIr⟩, hApin⟩ :=
    iff_shapes hok hn
  -- task #161 P5: the pin hit forgives the binder prop-ness datum too,
  -- so it no longer gives `ErasedEq` on the stored type itself.  It
  -- gives what this fact is for — the denotations agree —directly.
  have htyA : ∀ ψ : Name → Nat,
      denote m.cval env ψ 0 cvA.type = denote m.cval env ψ 0 propextA.type :=
    fun _ => denote_matchesPin hApin 0
  -- the `Eq` former's one level parameter is pinned to `1`
  have hsub : ∀ (φ : Name → Nat) (p : Name),
      p ∈ eqA.toConstantVal.levelParams →
      Level.substFn φ eqA.toConstantVal.levelParams
        [Level.zero.succ] p = 1 := by
    intro φ p hp
    have hlpEq : eqA.toConstantVal.levelParams
        = [Name.anonymous.str "u"] := rfl
    rw [hlpEq] at hp
    have hpu : p = Name.anonymous.str "u" := List.mem_singleton.mp hp
    subst hpu
    rfl
  have heqψ : ∀ φ : Name → Nat,
      Level.substFn φ eqA.toConstantVal.levelParams
        [Level.zero.succ] uN = 1 :=
    fun φ => hsub φ _ (List.Mem.head _)
  have hQmem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (m.cval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [.succ .zero])) ∈ˢ piC (univ 1)
        (fun A => piC A (fun _ => piC A (fun _ => univ 0))) := by
    intro ψ ρ
    obtain ⟨t, ht, hlaw⟩ := m.cval_memType hEq
      (Level.substFn ψ eqA.toConstantVal.levelParams [.succ .zero])
    rw [denote_eqA_typeS _ (heqψ ψ)] at ht
    obtain rfl := Option.some.inj ht
    exact (hlaw ρ).1
  have hden : ∀ ψ : Name → Nat,
      denoteClosed m.cval env ψ cvA.type
        = some (.pi (.sort 0) (.pi (.sort 0)
          (.pi (VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0])
            (VExpr.mkAppN (m.cval eqName (Level.substFn ψ
              eqA.toConstantVal.levelParams [.succ .zero]))
              [.sort 0, .bvar 2, .bvar 1])))) := by
    intro ψ
    rw [denoteClosed, htyA ψ]
    exact denote_propext_typeS hfI hlpI hEq ψ
  refine ⟨fun _ => .const .propext [], fun _ => trivial,
    fun _ _ _ => rfl, fun _ _ => trivial, fun ψ => ?_,
    fun _ _ => annotLeaf2_const V .propext fun _ => []⟩
  refine ⟨_, hden ψ, fun ρ => ⟨?_, ?_⟩⟩
  · -- the value is `pt`, and every fibre is `pt`-inhabited
    rw [interp_const]
    show (pt : V) ∈ˢ _
    rw [interp_pi]
    refine pt_mem_piC_iff.mpr fun A hA => ?_
    rw [interp_pi]
    refine pt_mem_piC_iff.mpr fun B hB => ?_
    rw [interp_pi]
    refine pt_mem_piC_iff.mpr fun w hw => ?_
    rw [interp_sort] at hA hB
    have hAB : A = B := by
      refine iff_forces_eqS m hfI hlpI hfIi hlpIi htyIi hfIr htyIr ψ
        (cons V B (cons V A ρ)) (w := w) hA hB ?_
      exact (hw : w ∈ˢ SetTheory.app (SetTheory.app
        (interp V (cons V B (cons V A ρ)) (m.cval iffName ψ)) A) B)
    rw [EqLawV.app₃ V m.eq_lawV hEq
      (Level.substFn ψ eqA.toConstantVal.levelParams [.succ .zero])
      (cons V w (cons V B (cons V A ρ))) (.sort 0) (.bvar 2) (.bvar 1)
      (by rw [interp_sort, heqψ ψ]; exact univ_mem_univ 0)
      (show A ∈ˢ (univ 0 : V) from hA)
      (show B ∈ˢ (univ 0 : V) from hB)]
    show (pt : V) ∈ˢ eqv A B
    exact hAB ▸ pt_mem_eqv_self A
  · -- the denoted type is truthful
    rw [AnnotOkV_pi]
    refine ⟨trivial, fun A hA => ?_⟩
    rw [AnnotOkV_pi]
    refine ⟨trivial, fun B hB => ?_⟩
    rw [interp_sort] at hA hB
    have hIm : ∀ ρ' : Nat → V, interp V ρ' (m.cval iffName ψ)
        ∈ˢ piC (univ 0 : V) fun _ =>
          piC (univ 0 : V) fun _ => (univ 0 : V) :=
      fun ρ' => iffVal_memS m hfI htyI ψ ρ'
    have hP : AnnotOkV V (cons V B (cons V A ρ))
        (VExpr.mkAppN (m.cval iffName ψ) [.bvar 1, .bvar 0]) := by
      show AnnotOkV V _ (.app (.app (m.cval iffName ψ) (.bvar 1))
        (.bvar 0))
      have h1 : AnnotOkV V (cons V B (cons V A ρ))
          (.app (m.cval iffName ψ) (.bvar 1)) := by
        rw [AnnotOkV_app]
        exact ⟨m.annot_okV _ _ _, trivial, _, _, hIm _, hA⟩
      rw [AnnotOkV_app]
      exact ⟨h1, trivial, _, _, app_mem_piC (hIm _) hA, hB⟩
    rw [AnnotOkV_pi]
    refine ⟨hP, fun w hw => ?_⟩
    have hQ := hQmem ψ (cons V w (cons V B (cons V A ρ)))
    have hU : (univ 0 : V) ∈ˢ univ 1 := univ_mem_univ 0
    show AnnotOkV V _ (.app (.app (.app (m.cval eqName
      (Level.substFn ψ eqA.toConstantVal.levelParams [.succ .zero]))
      (.sort 0)) (.bvar 2)) (.bvar 1))
    have h1m := app_mem_piC hQ hU
    have h2m := app_mem_piC h1m (show A ∈ˢ (univ 0 : V) from hA)
    have e1 : AnnotOkV V (cons V w (cons V B (cons V A ρ)))
        (.app (m.cval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [.succ .zero])) (.sort 0)) := by
      rw [AnnotOkV_app]
      exact ⟨m.annot_okV _ _ _, trivial, _, _, hQ, hU⟩
    have e2 : AnnotOkV V (cons V w (cons V B (cons V A ρ)))
        (.app (.app (m.cval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [.succ .zero])) (.sort 0))
          (.bvar 2)) := by
      rw [AnnotOkV_app]
      exact ⟨e1, trivial, _, _, h1m, hA⟩
    rw [AnnotOkV_app]
    exact ⟨e2, trivial, _, _, h2m, hB⟩

/-! ## `Classical.choice`

The witness is the layer's own `choice` constant, whose value
abstracts over the **double negation** `¬¬A` while the checker's pin
abstracts over the stored `Nonempty A`.  Both are propositions, and
both are `pt`-inhabited exactly when `A` is; so `prop_ext` identifies
the two domains and the layer's constant is literally a member of the
checker's pinned type.  Forcing `A` inhabited from a stored
`Nonempty A` witness is the recursor's job, at the constantly-`∅`
motive whose minor premise is vacuous over an empty `A`.
-/

/-- The stored `Nonempty` is a family of propositions. -/
theorem nonemptyVal_memS {env : Env} (m : EnvS V env)
    {cvN : ConstantVal} {capsN : IndCaps}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (htyN : cvN.type.erasePw.eraseNames
      = nonemptyA.toConstantVal.type.erasePw.eraseNames)
    (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (m.cval nonemptyName ψ)
      ∈ˢ piC (univ (ψ uN) : V) fun _ => (univ 0 : V) := by
  obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfN ψ
  rw [show (ConstantInfo.indInfo cvN capsN).toConstantVal = cvN
      from rfl,
    denoteClosed, denote_pinEq htyN 0] at ht
  simp [nonemptyA, ConstantInfo.toConstantVal, denote_forallE,
    denote_sort, Expr.instantiate1, Level.eval] at ht
  obtain rfl := ht
  have h1 := (hlaw ρ).1
  simp only [interp_pi, interp_sort] at h1
  exact h1

/-- The interpreted `Nonempty A` is a truth value. -/
theorem nonemptyVal_app_memS {env : Env} (m : EnvS V env)
    {cvN : ConstantVal} {capsN : IndCaps}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (htyN : cvN.type.erasePw.eraseNames
      = nonemptyA.toConstantVal.type.erasePw.eraseNames)
    (ψ : Name → Nat) (ρ : Nat → V) {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (interp V ρ (m.cval nonemptyName ψ)) A
      ∈ˢ (univ 0 : V) :=
  app_mem_piC (nonemptyVal_memS m hfN htyN ψ ρ) hA

/-- The stored `Nonempty.intro` inhabits its pinned type. -/
theorem nonemptyIntroVal_memS {env : Env} (m : EnvS V env)
    {cvN : ConstantVal} {capsN : IndCaps} {cvNi : ConstantVal}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (hfNi : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (htyNi : cvNi.type.erasePw.eraseNames
      = nonemptyIntroA.toConstantVal.type.erasePw.eraseNames)
    (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (m.cval nonemptyIntroName ψ)
      ∈ˢ piC (univ (ψ uN) : V) fun A =>
        piC A fun _ =>
          SetTheory.app (interp V ρ (m.cval nonemptyName ψ)) A := by
  obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfNi ψ
  rw [show (ConstantInfo.ctorInfo cvNi 1 1).toConstantVal = cvNi
      from rfl, denoteClosed,
    denote_pinEq htyNi 0] at ht
  have hsub : Level.substFn ψ [uN] [Level.param uN] = ψ :=
    funext fun _ => Level.substFn_map_param
  have hN : ∀ d, denote m.cval env ψ d
      (.const nonemptyName [.param uN])
        = some (m.cval nonemptyName ψ) := by
    intro d
    rw [denote_const, hfN]
    show (if [Level.param uN].length = cvN.levelParams.length then
        some (m.cval nonemptyName
          (Level.substFn ψ cvN.levelParams [Level.param uN]))
      else none) = _
    rw [hlpN, show nonemptyA.toConstantVal.levelParams = [uN] from rfl,
      ]
    simp only [List.length_cons, List.length_nil, reduceIte]
    rw [hsub]
  simp only [nonemptyName, uN] at hN
  simp [nonemptyIntroA, ConstantInfo.toConstantVal, denote_forallE,
    denote_sort, Expr.instantiate1, denote_app, denote_fvar,
    hN, Level.eval] at ht
  obtain rfl := ht
  have h1 := (hlaw ρ).1
  simp only [interp_pi, interp_sort, interp_app, interp_bvar,
    cons_zero, cons_succ,
    interp_closed (V := V) (m.cval_closed _ ψ) _ ρ] at h1
  exact h1

/-- The interpreted `Nonempty.intro A a` inhabits `Nonempty A`. -/
theorem nonemptyIntroVal_app₂_memS {env : Env} (m : EnvS V env)
    {cvN : ConstantVal} {capsN : IndCaps} {cvNi : ConstantVal}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (hfNi : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (htyNi : cvNi.type.erasePw.eraseNames
      = nonemptyIntroA.toConstantVal.type.erasePw.eraseNames)
    (ψ : Name → Nat) (ρ : Nat → V) {A a : V}
    (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app
        (interp V ρ (m.cval nonemptyIntroName ψ)) A) a
      ∈ˢ SetTheory.app (interp V ρ (m.cval nonemptyName ψ)) A :=
  app_mem_piC (app_mem_piC
    (nonemptyIntroVal_memS m hfN hlpN hfNi htyNi ψ ρ) hA) ha

/-- The stored `Nonempty.rec` inhabits its pinned type. -/
theorem nonemptyRecVal_memS {env : Env} (m : EnvS V env)
    {cvN : ConstantVal} {capsN : IndCaps} {cvNi cvNr : ConstantVal}
    {mI rP : Nat} {rulesN : List RecRule}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (hfNi : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hlpNi : cvNi.levelParams
      = nonemptyIntroA.toConstantVal.levelParams)
    (hfNr : env.find? nonemptyRecName
      = some (.recInfo cvNr mI rP rulesN))
    (htyNr : cvNr.type.erasePw.eraseNames
      = nonemptyRecA.toConstantVal.type.erasePw.eraseNames)
    (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (m.cval nonemptyRecName ψ)
      ∈ˢ piC (univ (ψ uN) : V) fun A =>
        piC (piC (SetTheory.app
            (interp V ρ (m.cval nonemptyName ψ)) A)
          fun _ => (univ 0 : V))
          fun M =>
          piC (piC A fun a => SetTheory.app M (SetTheory.app
              (SetTheory.app
                (interp V ρ (m.cval nonemptyIntroName ψ)) A) a))
            fun _ =>
            piC (SetTheory.app (interp V ρ (m.cval nonemptyName ψ)) A)
              fun t => SetTheory.app M t := by
  obtain ⟨t, ht, hlaw⟩ := m.cval_memType hfNr ψ
  rw [show (ConstantInfo.recInfo cvNr mI rP rulesN).toConstantVal = cvNr
      from rfl, denoteClosed,
    denote_pinEq htyNr 0] at ht
  have hsub : Level.substFn ψ [uN] [Level.param uN] = ψ :=
    funext fun _ => Level.substFn_map_param
  have hN : ∀ d, denote m.cval env ψ d
      (.const nonemptyName [.param uN])
        = some (m.cval nonemptyName ψ) := by
    intro d
    rw [denote_const, hfN]
    show (if [Level.param uN].length = cvN.levelParams.length then
        some (m.cval nonemptyName
          (Level.substFn ψ cvN.levelParams [Level.param uN]))
      else none) = _
    rw [hlpN, show nonemptyA.toConstantVal.levelParams = [uN] from rfl]
    simp only [List.length_cons, List.length_nil, reduceIte]
    rw [hsub]
  have hNi : ∀ d, denote m.cval env ψ d
      (.const nonemptyIntroName [.param uN])
        = some (m.cval nonemptyIntroName ψ) := by
    intro d
    rw [denote_const, hfNi]
    show (if [Level.param uN].length = cvNi.levelParams.length then
        some (m.cval nonemptyIntroName
          (Level.substFn ψ cvNi.levelParams [Level.param uN]))
      else none) = _
    rw [hlpNi,
      show nonemptyIntroA.toConstantVal.levelParams = [uN] from rfl]
    simp only [List.length_cons, List.length_nil, reduceIte]
    rw [hsub]
  simp only [nonemptyName, nonemptyIntroName, uN] at hN hNi
  simp [nonemptyRecA, ConstantInfo.toConstantVal, denote_forallE,
    denote_sort, Expr.instantiate1, denote_app, denote_fvar,
    hN, hNi, Level.eval] at ht
  obtain rfl := ht
  have h1 := (hlaw ρ).1
  simp only [interp_pi, interp_sort, interp_app, interp_bvar,
    cons_zero, cons_succ,
    interp_closed (V := V) (m.cval_closed _ ψ) _ ρ] at h1
  exact h1

/-- A witness of the interpreted `Nonempty A` forces `A` inhabited,
through the recursor at the constantly-`∅` motive. -/
theorem nonemptyVal_forcesS {env : Env} (m : EnvS V env)
    {cvN : ConstantVal} {capsN : IndCaps} {cvNi cvNr : ConstantVal}
    {mI rP : Nat} {rulesN : List RecRule}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (hfNi : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hlpNi : cvNi.levelParams
      = nonemptyIntroA.toConstantVal.levelParams)
    (hfNr : env.find? nonemptyRecName
      = some (.recInfo cvNr mI rP rulesN))
    (htyNr : cvNr.type.erasePw.eraseNames
      = nonemptyRecA.toConstantVal.type.erasePw.eraseNames)
    (ψ : Name → Nat) (ρ : Nat → V) {A h : V} (hA : A ∈ˢ univ (ψ uN))
    (hh : h ∈ˢ SetTheory.app (interp V ρ (m.cval nonemptyName ψ)) A) :
    ∃ x, x ∈ˢ A := by
  refine Classical.byContradiction fun hno => ?_
  have hM : lamC (SetTheory.app
        (interp V ρ (m.cval nonemptyName ψ)) A) (fun _ => (empty : V))
      ∈ˢ piC (SetTheory.app (interp V ρ (m.cval nonemptyName ψ)) A)
        fun _ => (univ 0 : V) :=
    lamC_mem fun _ _ => empty_mem_univ 0
  have r2 := app_mem_piC (app_mem_piC
    (nonemptyRecVal_memS m hfN hlpN hfNi hlpNi hfNr htyNr ψ ρ) hA) hM
  have hminor : (pt : V) ∈ˢ piC A fun a =>
      SetTheory.app (lamC (SetTheory.app
          (interp V ρ (m.cval nonemptyName ψ)) A)
        (fun _ => (empty : V)))
        (SetTheory.app (SetTheory.app
          (interp V ρ (m.cval nonemptyIntroName ψ)) A) a) :=
    pt_mem_piC_iff.mpr fun a ha => absurd ⟨a, ha⟩ hno
  have r4 := app_mem_piC (app_mem_piC r2 hminor) hh
  rw [app_lamC hh] at r4
  exact not_mem_empty _ r4

/-- **The two domains agree.**  The layer's `¬¬A` and the checker's
stored `Nonempty A` are propositions with the same inhabitation, hence
the same set. -/
theorem dneg_eq_nonemptyS {env : Env} (m : EnvS V env)
    {cvN : ConstantVal} {capsN : IndCaps} {cvNi cvNr : ConstantVal}
    {mI rP : Nat} {rulesN : List RecRule}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (htyN : cvN.type.erasePw.eraseNames
      = nonemptyA.toConstantVal.type.erasePw.eraseNames)
    (hfNi : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hlpNi : cvNi.levelParams
      = nonemptyIntroA.toConstantVal.levelParams)
    (htyNi : cvNi.type.erasePw.eraseNames
      = nonemptyIntroA.toConstantVal.type.erasePw.eraseNames)
    (hfNr : env.find? nonemptyRecName
      = some (.recInfo cvNr mI rP rulesN))
    (htyNr : cvNr.type.erasePw.eraseNames
      = nonemptyRecA.toConstantVal.type.erasePw.eraseNames)
    (ψ : Name → Nat) (ρ : Nat → V) {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    piC (piC A fun _ => (empty : V)) (fun _ => (empty : V))
      = SetTheory.app (interp V ρ (m.cval nonemptyName ψ)) A := by
  have hNE := nonemptyVal_app_memS m hfN htyN ψ ρ hA
  have hdn : piC (piC A fun _ => (empty : V)) (fun _ => (empty : V))
      ∈ˢ (univ 0 : V) := by
    rw [univ_zero]
    exact piC_prop_mem_univZero fun _ _ =>
      univ_zero (V := V) ▸ empty_mem_univ 0
  refine prop_ext hdn hNE (fun hpt => ?_) (fun hpt => ?_)
  · obtain ⟨x, hx⟩ := exists_mem_of_dneg V hpt
    have hi := nonemptyIntroVal_app₂_memS m hfN hlpN hfNi htyNi ψ ρ
      hA hx
    rwa [mem_univ_zero hNE hi] at hi
  · obtain ⟨x, hx⟩ := nonemptyVal_forcesS m hfN hlpN hfNi hlpNi hfNr
      htyNr ψ ρ hA hpt
    exact pt_mem_piC_iff.mpr fun g hg =>
      absurd (app_mem_piC hg hx) (not_mem_empty _)

/-- `Classical.choice`'s pinned type, denoted. -/
theorem denote_choice_typeS {cval : TConstVal} {env : Env}
    {cvN : ConstantVal} {capsN : IndCaps}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (ψ : Name → Nat) :
    denote cval env ψ 0 choiceA.type =
      some (.pi (.sort (ψ uN))
        (.pi (.app (cval nonemptyName ψ) (.bvar 0)) (.bvar 1))) := by
  have hsub : Level.substFn ψ [uN] [Level.param uN] = ψ :=
    funext fun _ => Level.substFn_map_param
  have hN : ∀ d, denote cval env ψ d
      (.const nonemptyName [.param uN])
        = some (cval nonemptyName ψ) := by
    intro d
    rw [denote_const, hfN]
    show (if [Level.param uN].length = cvN.levelParams.length then
        some (cval nonemptyName
          (Level.substFn ψ cvN.levelParams [Level.param uN]))
      else none) = _
    rw [hlpN, show nonemptyA.toConstantVal.levelParams = [uN] from rfl]
    simp only [List.length_cons, List.length_nil, reduceIte]
    rw [hsub]
  simp only [nonemptyName, uN] at hN
  simp [choiceA, denote_forallE, denote_sort, Expr.instantiate1,
    denote_app, denote_fvar, hN, Level.eval]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 1600000 in
/-- **The `Classical.choice` half of the key.**  The witness is the
layer's own `choice` constant; `dneg_eq_nonemptyS` identifies its
double-negation domain with the checker's stored `Nonempty`. -/
theorem choiceKeyS : ChoiceKeyS V := by
  intro env m cvA hok hn hfresh
  obtain ⟨⟨cvN, capsN, hfN, hlpN, htyN⟩, ⟨cvNi, hfNi, hlpNi, htyNi⟩,
    ⟨cvNr, mI, rP, rulesN, hfNr, hlpNr, htyNr⟩, hApin⟩ :=
    nonempty_shapes hok hn
  have hlpA : cvA.levelParams = choiceA.levelParams :=
    (matchesPin_invT hApin).2
  -- as at `propextKeyS`: the pin hit gives the denotation equality
  -- directly (task #161 P5).
  have htyA : ∀ ψ : Name → Nat,
      denote m.cval env ψ 0 cvA.type = denote m.cval env ψ 0 choiceA.type :=
    fun _ => denote_matchesPin hApin 0
  have hden : ∀ ψ : Name → Nat,
      denoteClosed m.cval env ψ cvA.type
        = some (.pi (.sort (ψ uN))
          (.pi (.app (m.cval nonemptyName ψ) (.bvar 0))
            (.bvar 1))) := by
    intro ψ
    rw [denoteClosed, htyA ψ]
    exact denote_choice_typeS hfN hlpN ψ
  refine ⟨fun ψ => .const .choice [ψ uN], fun _ => trivial, ?_,
    fun _ _ => trivial, fun ψ => ?_,
    fun _ _ => annotLeaf2_const V .choice fun ψ => [ψ uN]⟩
  · intro φ₁ φ₂ hp
    have : φ₁ uN = φ₂ uN := by
      refine hp uN ?_
      rw [hlpA, show choiceA.levelParams = [uN] from rfl]
      exact List.Mem.head _
    dsimp only
    rw [this]
  refine ⟨_, hden ψ, fun ρ => ⟨?_, ?_⟩⟩
  · rw [interp_const]
    show choiceV V (ψ uN) ∈ˢ _
    rw [interp_pi, choiceV]
    refine lamC_mem fun A hA => ?_
    have hA : A ∈ˢ (univ (ψ uN) : V) := hA
    have hAe := dneg_eq_nonemptyS m hfN hlpN htyN hfNi hlpNi htyNi hfNr
      htyNr ψ (cons V A ρ) hA
    show lamC (piC (piC A fun _ => (empty : V)) fun _ => (empty : V))
      (fun _ => schoice A) ∈ˢ _
    rw [interp_pi, hAe]
    refine lamC_mem fun h hh => ?_
    show schoice A ∈ˢ A
    obtain ⟨x, hx⟩ := exists_mem_of_dneg V (hAe ▸ hh)
    exact schoice_mem hx
  · rw [AnnotOkV_pi]
    refine ⟨trivial, fun A hA => ?_⟩
    have hA : A ∈ˢ (univ (ψ uN) : V) := hA
    rw [AnnotOkV_pi]
    refine ⟨?_, fun _ _ => trivial⟩
    rw [AnnotOkV_app]
    exact ⟨m.annot_okV _ _ _, trivial, _, _,
      nonemptyVal_memS m hfN htyN ψ _, hA⟩

/-- **`StdAxiomKeyS`, discharged.** -/
theorem stdAxiomKeyS : StdAxiomKeyS V :=
  stdAxiomKeyS_of propextKeyS choiceKeyS

end Setlec.SetR
