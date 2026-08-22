import Setlec.Kernel.StdAxioms
import Setlec.Model.Basis.Util
import Setlec.Model.Basis.Eq.Install

/-!
# Standard axioms: models for `propext` and `Classical.choice`

The checker accepts exactly the two standard axioms, with their types
pinned up to the exporter's unstable hygienic binder names
(`ConstantVal.matchesPin`).  This module provides

* the bridge from `Expr.eraseNames`-equality to `Expr.ErasedEq`, so
  the interpretation of a stored type can be transported to the pinned
  type (the interpretation never reads what `eraseNames` erases);
* set-theoretic values for the two axioms together with the `hkey`
  membership facts `extend_basis_one` needs.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open SetTheory Expr

/-- Name erasure only changes what `ErasedEq` ignores. -/
theorem Expr.ErasedEq.of_eraseNames :
    ∀ {a b : Expr}, a.eraseNames = b.eraseNames → ErasedEq a b
  | .bvar _, b, h => by
    match b, h with
    | .bvar _, h =>
      simp only [eraseNames, Expr.bvar.injEq] at h
      exact h
  | .fvar _ _ tya, b, h => by
    match b, h with
    | .fvar _ _ tyb, h =>
      simp only [eraseNames, Expr.fvar.injEq] at h
      exact h.1
  | .sort _, b, h => by
    match b, h with
    | .sort _, h =>
      simp only [eraseNames, Expr.sort.injEq] at h
      exact h
  | .const _ _, b, h => by
    match b, h with
    | .const _ _, h =>
      simp only [eraseNames, Expr.const.injEq] at h
      exact h
  | .app fa aa, b, h => by
    match b, h with
    | .app fb ab, h =>
      simp only [eraseNames, Expr.app.injEq] at h
      exact ⟨of_eraseNames h.1, of_eraseNames h.2⟩
  | .lam _ tya ba ma, b, h => by
    match b, h with
    | .lam _ tyb bb mb, h =>
      simp only [eraseNames, Expr.lam.injEq] at h
      exact ⟨h.2.2.2, of_eraseNames h.2.1, of_eraseNames h.2.2.1⟩
  | .forallE _ tya ba ma, b, h => by
    match b, h with
    | .forallE _ tyb bb mb, h =>
      simp only [eraseNames, Expr.forallE.injEq] at h
      exact ⟨h.2.2.2, of_eraseNames h.2.1, of_eraseNames h.2.2.1⟩
  | .letE _ tya va ba, b, h => by
    match b, h with
    | .letE _ tyb vb bb, h =>
      simp only [eraseNames, Expr.letE.injEq] at h
      exact ⟨of_eraseNames h.2.1, of_eraseNames h.2.2.1,
        of_eraseNames h.2.2.2⟩
  | .lit _, b, h => by
    match b, h with
    | .lit _, h =>
      simp only [eraseNames, Expr.lit.injEq] at h
      exact h
  | .proj _ _ ea, b, h => by
    match b, h with
    | .proj _ _ eb, h =>
      simp only [eraseNames, Expr.proj.injEq] at h
      exact ⟨h.1, h.2.1, of_eraseNames h.2.2⟩

variable {V : Type u} [SetTheory V]

/-- A `matchesPin` hit lets the closed interpretation be computed on
the pinned type instead of the stored one. -/
theorem interpClosed_matchesPin {cval : ConstVal V} {env : Env}
    {ψ : Name → Nat} {cv pin : ConstantVal}
    (h : ConstantVal.matchesPin cv pin = true) :
    interpClosed V cval env ψ cv.type = interpClosed V cval env ψ pin.type := by
  simp only [ConstantVal.matchesPin, Bool.and_eq_true, beq_iff_eq] at h
  exact interp_erasedEq (Expr.ErasedEq.of_eraseNames h.2) 0 (rho0 V)

/-- Name and level-parameter components of a `matchesPin` hit. -/
theorem ConstantVal.matchesPin_inv {cv pin : ConstantVal}
    (h : ConstantVal.matchesPin cv pin = true) :
    cv.name = pin.name ∧ cv.levelParams = pin.levelParams := by
  simp only [ConstantVal.matchesPin, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-! ## Generic membership helpers -/

variable {env : Env} {ψ : Name → Nat}

/-- Propositional `pi`-introduction: `pt` inhabits `pi 0 A B` as soon as
every fibre over `A` is inhabited (the `v = 0` case of `lam_mem`, with
the abstraction collapsed by `lam_zero`; the witness function comes from
meta-level choice). -/
theorem pt_mem_pi_zero {A : V} {B : V → V}
    (h : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) : SetTheory.pt ∈ˢ pi 0 A B := by
  have hex : ∀ x : V, ∃ y, x ∈ˢ A → y ∈ˢ B x := fun x => by
    by_cases hx : x ∈ˢ A
    · obtain ⟨y, hy⟩ := h x hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨SetTheory.pt, fun hc => absurd hc hx⟩
  have hm := lam_mem (V := V) (v := 0) (A := A) (B := B)
    (F := fun x => (hex x).choose)
    (fun x hx => (hex x).choose_spec hx)
  rwa [lam_zero] at hm

/-- Propositional `pi`-formation lands in `univ 0`. -/
theorem pi0_mem_univ0 {u : Nat} {A : V} {B : V → V} (hA : A ∈ˢ univ u)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) : pi 0 A B ∈ˢ univ 0 := by
  simpa using pi_mem_univ hA hB

/-! ## `propext`

The value is the proof point; the membership fact interprets the pinned
type (over the stored `Iff` family and the pinned `Eq` basis) and shows
`A = B` from any interpreted `Iff A B` witness, through the stored
`Iff.rec`'s membership fact at a `Prop`-valued motive `fun _ => eqv A B`.
-/

/-- The set-theoretic value of `propext`: a proof point. -/
def propextVal (V : Type u) [SetTheory V] : V := SetTheory.pt

/-- Interpretation of `Iff`'s pinned type, computed. -/
theorem interp_iff_type {cval : ConstVal V} :
    interpClosed V cval env ψ iffA.toConstantVal.type =
      some (pi 1 (univ 0) fun _ => pi 1 (univ 0) fun _ => univ 0) := by
  simp only [interpClosed, iffA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD]
  simp [interpExpr, Expr.instantiate1, updV]
  try rfl

/-- The stored `Iff` value is a member of the interpreted pinned type. -/
theorem iffVal_mem (m : EnvModel V env)
    {cvI : ConstantVal} {caps : IndCaps}
    (hIf : env.find? iffName = some (.indInfo cvI caps))
    (hIp : ConstantVal.matchesPin cvI iffA.toConstantVal = true)
    (ψ' : Name → Nat) :
    m.val iffName ψ' ∈ˢ
      pi 1 (univ 0) fun _ => pi 1 (univ 0) fun _ => univ 0 := by
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hIf) ψ'
  rw [show (ConstantInfo.indInfo cvI caps).toConstantVal = cvI from rfl] at ht
  rw [interpClosed_matchesPin hIp, interp_iff_type] at ht
  obtain rfl := Option.some.inj ht
  have hname : cvI.name = iffName := (ConstantVal.matchesPin_inv hIp).1
  rw [show (ConstantInfo.indInfo cvI caps).name = cvI.name from rfl,
    hname] at hmem
  exact hmem

/-- The interpreted `Iff A B` is a truth value. -/
theorem iffVal_app₂_mem (m : EnvModel V env)
    {cvI : ConstantVal} {caps : IndCaps}
    (hIf : env.find? iffName = some (.indInfo cvI caps))
    (hIp : ConstantVal.matchesPin cvI iffA.toConstantVal = true)
    (ψ' : Name → Nat) {A B : V} (hA : A ∈ˢ univ 0) (hB : B ∈ˢ univ 0) :
    SetTheory.app (SetTheory.app (m.val iffName ψ') A) B ∈ˢ univ 0 := by
  have h1 := app_mem (iffVal_mem m hIf hIp ψ') hA (fun X hX => by
    simpa using pi_mem_univ (u := 1) (v := 1) (B := fun _ => univ 0)
      (univ_mem_univ 0) (fun _ _ => univ_mem_univ 0))
  exact app_mem h1 hB (fun _ _ => univ_mem_univ 0)

/-- Interpretation of `Iff.intro`'s pinned type, computed. -/
theorem interp_iffIntro_type {cval : ConstVal V}
    {cvI : ConstantVal} {caps : IndCaps}
    (hIf : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = []) :
    interpClosed V cval env ψ iffIntroA.toConstantVal.type =
      some (pi 0 (univ 0) fun A => pi 0 (univ 0) fun B =>
        pi 0 (pi 0 A fun _ => B) fun _ =>
          pi 0 (pi 0 B fun _ => A) fun _ =>
            SetTheory.app (SetTheory.app (cval iffName ψ) A) B) := by
  have hIf' : env.find? (Name.anonymous.str "Iff") =
      some (.indInfo cvI caps) := hIf
  simp only [interpClosed, iffIntroA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD, hIf', hlpI,
    List.length_cons, List.length_nil, reduceIte, Level.substFn_nil]
  simp [interpExpr, Expr.instantiate1, updV, iffName, Level.substFn_nil,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- The stored `Iff.intro` value is a member of the interpreted pinned
type. -/
theorem iffIntroVal_mem (m : EnvModel V env)
    {cvI : ConstantVal} {caps : IndCaps}
    (hIf : env.find? iffName = some (.indInfo cvI caps))
    (hIp : ConstantVal.matchesPin cvI iffA.toConstantVal = true)
    {cvIi : ConstantVal}
    (hIif : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hIip : ConstantVal.matchesPin cvIi iffIntroA.toConstantVal = true)
    (ψ' : Name → Nat) :
    m.val iffIntroName ψ' ∈ˢ
      pi 0 (univ 0) fun A => pi 0 (univ 0) fun B =>
        pi 0 (pi 0 A fun _ => B) fun _ =>
          pi 0 (pi 0 B fun _ => A) fun _ =>
            SetTheory.app (SetTheory.app (m.val iffName ψ') A) B := by
  have hlpI : cvI.levelParams = [] := (ConstantVal.matchesPin_inv hIp).2
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hIif) ψ'
  rw [show (ConstantInfo.ctorInfo cvIi 2 2).toConstantVal = cvIi from rfl]
    at ht
  rw [interpClosed_matchesPin hIip, interp_iffIntro_type hIf hlpI] at ht
  obtain rfl := Option.some.inj ht
  have hname : cvIi.name = iffIntroName := (ConstantVal.matchesPin_inv hIip).1
  rw [show (ConstantInfo.ctorInfo cvIi 2 2).name = cvIi.name from rfl,
    hname] at hmem
  exact hmem

/-- The interpreted `Iff.intro A B mp mpr` inhabits the interpreted
`Iff A B`. -/
theorem iffIntroVal_app₄_mem (m : EnvModel V env)
    {cvI : ConstantVal} {caps : IndCaps}
    (hIf : env.find? iffName = some (.indInfo cvI caps))
    (hIp : ConstantVal.matchesPin cvI iffA.toConstantVal = true)
    {cvIi : ConstantVal}
    (hIif : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hIip : ConstantVal.matchesPin cvIi iffIntroA.toConstantVal = true)
    (ψ' : Name → Nat) {A B mp mpr : V}
    (hA : A ∈ˢ univ 0) (hB : B ∈ˢ univ 0)
    (hmp : mp ∈ˢ pi 0 A fun _ => B) (hmpr : mpr ∈ˢ pi 0 B fun _ => A) :
    SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (m.val iffIntroName ψ') A) B) mp) mpr ∈ˢ
      SetTheory.app (SetTheory.app (m.val iffName ψ') A) B := by
  have hF : ∀ X Y : V, X ∈ˢ univ 0 → Y ∈ˢ univ 0 →
      SetTheory.app (SetTheory.app (m.val iffName ψ') X) Y ∈ˢ univ 0 :=
    fun X Y hX hY => iffVal_app₂_mem m hIf hIp ψ' hX hY
  have h1 := app_mem (iffIntroVal_mem m hIf hIp hIif hIip ψ') hA (fun X hX =>
    pi0_mem_univ0 (univ_mem_univ 0) fun Y hY =>
      pi0_mem_univ0 (pi0_mem_univ0 hX fun _ _ => hY) fun _ _ =>
        pi0_mem_univ0 (pi0_mem_univ0 hY fun _ _ => hX) fun _ _ =>
          hF X Y hX hY)
  have h2 := app_mem h1 hB (fun Y hY =>
    pi0_mem_univ0 (pi0_mem_univ0 hA fun _ _ => hY) fun _ _ =>
      pi0_mem_univ0 (pi0_mem_univ0 hY fun _ _ => hA) fun _ _ =>
        hF A Y hA hY)
  have h3 := app_mem h2 hmp (fun _ _ =>
    pi0_mem_univ0 (pi0_mem_univ0 hB fun _ _ => hA) fun _ _ => hF A B hA hB)
  exact app_mem h3 hmpr (fun _ _ => hF A B hA hB)

/-- Interpretation of `Iff.rec`'s pinned type at a `Prop` motive level,
computed. -/
theorem interp_iffRec_type {cval : ConstVal V} {ψ0 : Name → Nat}
    (h0 : ψ0 uN = 0)
    {cvI : ConstantVal} {caps : IndCaps}
    (hIf : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    {cvIi : ConstantVal}
    (hIif : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hlpIi : cvIi.levelParams = []) :
    interpClosed V cval env ψ0 iffRecA.toConstantVal.type =
      some (pi 0 (univ 0) fun A => pi 0 (univ 0) fun B =>
        pi 0 (pi 1 (SetTheory.app (SetTheory.app (cval iffName ψ0) A) B)
            fun _ => univ 0) fun M =>
          pi 0 (pi 0 (pi 0 A fun _ => B) fun mp =>
              pi 0 (pi 0 B fun _ => A) fun mpr =>
                SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (cval iffIntroName ψ0) A) B) mp) mpr))
            fun _ =>
            pi 0 (SetTheory.app (SetTheory.app (cval iffName ψ0) A) B)
              fun t => SetTheory.app M t) := by
  have hIf' : env.find? (Name.anonymous.str "Iff") =
      some (.indInfo cvI caps) := hIf
  have hIif' : env.find? ((Name.anonymous.str "Iff").str "intro") =
      some (.ctorInfo cvIi 2 2) := hIif
  have h0' : ψ0 (Name.anonymous.str "u") = 0 := h0
  simp only [interpClosed, iffRecA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD, hIf', hIif', hlpI,
    hlpIi, List.length_cons, List.length_nil, reduceIte, Level.substFn_nil,
    h0']
  simp [interpExpr, Expr.instantiate1, updV, iffName, Level.substFn_nil, h0',
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- The stored `Iff.rec` value is a member of the interpreted pinned
type, at a `Prop` motive level. -/
theorem iffRecVal_mem (m : EnvModel V env)
    {cvI : ConstantVal} {caps : IndCaps}
    (hIf : env.find? iffName = some (.indInfo cvI caps))
    (hIp : ConstantVal.matchesPin cvI iffA.toConstantVal = true)
    {cvIi : ConstantVal}
    (hIif : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hIip : ConstantVal.matchesPin cvIi iffIntroA.toConstantVal = true)
    {cvIr : ConstantVal} {rules : List RecRule}
    (hIrf : env.find? iffRecName = some (.recInfo cvIr 4 4 rules))
    (hIrp : ConstantVal.matchesPin cvIr iffRecA.toConstantVal = true)
    {ψ0 : Name → Nat} (h0 : ψ0 uN = 0) :
    m.val iffRecName ψ0 ∈ˢ
      pi 0 (univ 0) fun A => pi 0 (univ 0) fun B =>
        pi 0 (pi 1 (SetTheory.app (SetTheory.app (m.val iffName ψ0) A) B)
            fun _ => univ 0) fun M =>
          pi 0 (pi 0 (pi 0 A fun _ => B) fun mp =>
              pi 0 (pi 0 B fun _ => A) fun mpr =>
                SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (m.val iffIntroName ψ0) A) B) mp) mpr))
            fun _ =>
            pi 0 (SetTheory.app (SetTheory.app (m.val iffName ψ0) A) B)
              fun t => SetTheory.app M t := by
  have hlpI : cvI.levelParams = [] := (ConstantVal.matchesPin_inv hIp).2
  have hlpIi : cvIi.levelParams = [] := (ConstantVal.matchesPin_inv hIip).2
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hIrf) ψ0
  rw [show (ConstantInfo.recInfo cvIr 4 4 rules).toConstantVal = cvIr
    from rfl] at ht
  rw [interpClosed_matchesPin hIrp,
    interp_iffRec_type h0 hIf hlpI hIif hlpIi] at ht
  obtain rfl := Option.some.inj ht
  have hname : cvIr.name = iffRecName := (ConstantVal.matchesPin_inv hIrp).1
  rw [show (ConstantInfo.recInfo cvIr 4 4 rules).name = cvIr.name
    from rfl, hname] at hmem
  exact hmem

/-- Interpreted `Iff` forces equality of truth values: any witness of
the interpreted `Iff A B` yields `A = B`, through the stored recursor's
membership fact at the motive `fun _ => eqv A B`. -/
theorem iff_forces_eq (m : EnvModel V env)
    {cvI : ConstantVal} {caps : IndCaps}
    (hIf : env.find? iffName = some (.indInfo cvI caps))
    (hIp : ConstantVal.matchesPin cvI iffA.toConstantVal = true)
    {cvIi : ConstantVal}
    (hIif : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hIip : ConstantVal.matchesPin cvIi iffIntroA.toConstantVal = true)
    {cvIr : ConstantVal} {rules : List RecRule}
    (hIrf : env.find? iffRecName = some (.recInfo cvIr 4 4 rules))
    (hIrp : ConstantVal.matchesPin cvIr iffRecA.toConstantVal = true)
    (ψ' : Name → Nat) {A B w : V} (hA : A ∈ˢ univ 0) (hB : B ∈ˢ univ 0)
    (hw : w ∈ˢ SetTheory.app (SetTheory.app (m.val iffName ψ') A) B) :
    A = B := by
  have hlpI : cvI.levelParams = [] := (ConstantVal.matchesPin_inv hIp).2
  have hlpIi : cvIi.levelParams = [] := (ConstantVal.matchesPin_inv hIip).2
  -- values of the parameterless family members do not read the assignment
  have hIval : ∀ ψ'' : Name → Nat,
      m.val iffName ψ'' = m.val iffName ψ' := fun ψ'' =>
    m.val_params _ _ hIf ψ'' ψ' (by
      rw [show (ConstantInfo.indInfo cvI caps).toConstantVal = cvI from rfl,
        hlpI]
      intro p hp; cases hp)
  have hIival : ∀ ψ'' : Name → Nat,
      m.val iffIntroName ψ'' = m.val iffIntroName ψ' := fun ψ'' =>
    m.val_params _ _ hIif ψ'' ψ' (by
      rw [show (ConstantInfo.ctorInfo cvIi 2 2).toConstantVal = cvIi
        from rfl, hlpIi]
      intro p hp; cases hp)
  -- the recursor's membership fact at the all-zero assignment
  have hvR := iffRecVal_mem m hIf hIp hIif hIip hIrf hIrp
    (ψ0 := fun _ => 0) rfl
  rw [hIval (fun _ => 0), hIival (fun _ => 0)] at hvR
  have hF : ∀ X Y : V, X ∈ˢ univ 0 → Y ∈ˢ univ 0 →
      SetTheory.app (SetTheory.app (m.val iffName ψ') X) Y ∈ˢ univ 0 :=
    fun X Y hX hY => iffVal_app₂_mem m hIf hIp ψ' hX hY
  have hIII : ∀ X Y mp' mpr' : V, X ∈ˢ univ 0 → Y ∈ˢ univ 0 →
      mp' ∈ˢ pi 0 X (fun _ => Y) → mpr' ∈ˢ pi 0 Y (fun _ => X) →
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (m.val iffIntroName ψ') X) Y) mp') mpr' ∈ˢ
        SetTheory.app (SetTheory.app (m.val iffName ψ') X) Y :=
    fun X Y mp' mpr' hX hY hmp' hmpr' =>
      iffIntroVal_app₄_mem m hIf hIp hIif hIip ψ' hX hY hmp' hmpr'
  -- the motive: constantly `eqv A B`, a genuine graph at level 1
  have hM : (SetTheory.lam 1
        (SetTheory.app (SetTheory.app (m.val iffName ψ') A) B)
        fun _ => eqv A B) ∈ˢ
      pi 1 (SetTheory.app (SetTheory.app (m.val iffName ψ') A) B)
        fun _ => univ 0 :=
    lam_mem fun _ _ => eqv_mem_univ A B
  have hMbeta : ∀ t, t ∈ˢ SetTheory.app (SetTheory.app
        (m.val iffName ψ') A) B →
      SetTheory.app (SetTheory.lam 1
        (SetTheory.app (SetTheory.app (m.val iffName ψ') A) B)
        fun _ => eqv A B) t = eqv A B :=
    fun t ht => app_lam (B := fun _ => univ 0) ht
      (fun _ _ => eqv_mem_univ A B) (fun _ _ => univ_mem_univ 0)
  -- universe scaffolding for the elimination chain
  have hMS : ∀ X Y : V, X ∈ˢ univ 0 → Y ∈ˢ univ 0 →
      (pi 1 (SetTheory.app (SetTheory.app (m.val iffName ψ') X) Y)
        fun _ => univ 0) ∈ˢ univ 1 := fun X Y hX hY => by
    simpa using pi_mem_univ (u := 0) (v := 1) (B := fun _ => univ 0)
      (hF X Y hX hY) (fun _ _ => univ_mem_univ 0)
  have hfun0 : ∀ X Y : V, X ∈ˢ univ 0 → Y ∈ˢ univ 0 →
      (pi 0 X fun _ => Y) ∈ˢ univ 0 :=
    fun X Y hX hY => pi0_mem_univ0 hX (fun _ _ => hY)
  have hminorU : ∀ X Y M' : V, X ∈ˢ univ 0 → Y ∈ˢ univ 0 →
      M' ∈ˢ (pi 1 (SetTheory.app (SetTheory.app (m.val iffName ψ') X) Y)
        fun _ => univ 0) →
      (pi 0 (pi 0 X fun _ => Y) fun mp' =>
        pi 0 (pi 0 Y fun _ => X) fun mpr' =>
          SetTheory.app M' (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (m.val iffIntroName ψ') X) Y) mp') mpr')) ∈ˢ
        univ 0 := by
    intro X Y M' hX hY hM'
    refine pi0_mem_univ0 (hfun0 X Y hX hY) fun mp' hmp' => ?_
    refine pi0_mem_univ0 (hfun0 Y X hY hX) fun mpr' hmpr' => ?_
    exact app_mem hM' (hIII X Y mp' mpr' hX hY hmp' hmpr')
      (fun _ _ => univ_mem_univ 0)
  have htail : ∀ X Y M' : V, X ∈ˢ univ 0 → Y ∈ˢ univ 0 →
      M' ∈ˢ (pi 1 (SetTheory.app (SetTheory.app (m.val iffName ψ') X) Y)
        fun _ => univ 0) →
      (pi 0 (SetTheory.app (SetTheory.app (m.val iffName ψ') X) Y)
        fun t => SetTheory.app M' t) ∈ˢ univ 0 := by
    intro X Y M' hX hY hM'
    exact pi0_mem_univ0 (hF X Y hX hY)
      (fun t ht => app_mem hM' ht (fun _ _ => univ_mem_univ 0))
  -- eliminate down the recursor's telescope
  have r1 := app_mem hvR hA (fun X hX =>
    pi0_mem_univ0 (univ_mem_univ 0) fun Y hY =>
      pi0_mem_univ0 (hMS X Y hX hY) fun M' hM' =>
        pi0_mem_univ0 (hminorU X Y M' hX hY hM')
          (fun _ _ => htail X Y M' hX hY hM'))
  have r2 := app_mem r1 hB (fun Y hY =>
    pi0_mem_univ0 (hMS A Y hA hY) fun M' hM' =>
      pi0_mem_univ0 (hminorU A Y M' hA hY hM')
        (fun _ _ => htail A Y M' hA hY hM'))
  have r3 := app_mem r2 hM (fun M' hM' =>
    pi0_mem_univ0 (hminorU A B M' hA hB hM')
      (fun _ _ => htail A B M' hA hB hM'))
  -- the minor premise: both directions inhabited forces `A = B`, and
  -- then the motive's fibre `eqv A B` is inhabited
  have hminor : SetTheory.pt ∈ˢ
      pi 0 (pi 0 A fun _ => B) fun mp' =>
        pi 0 (pi 0 B fun _ => A) fun mpr' =>
          SetTheory.app (SetTheory.lam 1
              (SetTheory.app (SetTheory.app (m.val iffName ψ') A) B)
              fun _ => eqv A B)
            (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
              (m.val iffIntroName ψ') A) B) mp') mpr') := by
    refine pt_mem_pi_zero fun mp' hmp' =>
      ⟨SetTheory.pt, pt_mem_pi_zero fun mpr' hmpr' => ?_⟩
    have hAB : A = B := by
      refine prop_ext hA hB ?_ ?_
      · intro hptA
        have h1 := app_mem hmp' hptA (fun _ _ => hB)
        rwa [mem_univ_zero hB h1] at h1
      · intro hptB
        have h1 := app_mem hmpr' hptB (fun _ _ => hA)
        rwa [mem_univ_zero hA h1] at h1
    rw [hMbeta _ (hIII A B mp' mpr' hA hB hmp' hmpr')]
    exact ⟨SetTheory.pt, hAB ▸ pt_mem_eqv_self A⟩
  have r4 := app_mem r3 hminor (fun _ _ => htail A B _ hA hB hM)
  have r5 := app_mem r4 hw
    (fun t ht => app_mem hM ht (fun _ _ => univ_mem_univ 0))
  rw [hMbeta w hw] at r5
  exact mem_eqv r5

/-- The level assignment `Eq`'s value sees inside `propext`'s type
(`Eq` is instantiated at level `1` there). -/
def pxψ (ψ : Name → Nat) : Name → Nat :=
  Level.substFn ψ [uN] [Level.succ Level.zero]

theorem pxψ_uN (ψ : Name → Nat) : pxψ ψ uN = 1 := by
  simp [pxψ, Level.substFn, Level.eval]

/-- Interpretation of `propext`'s pinned type, computed. -/
theorem interp_propext_type {cval : ConstVal V}
    (hE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ'' : Name → Nat, cval eqName ψ'' = eqVal V ψ'')
    {cvI : ConstantVal} {caps : IndCaps}
    (hIf : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = []) :
    interpClosed V cval env ψ propextA.type =
      some (pi 0 (univ 0) fun A => pi 0 (univ 0) fun B =>
        pi 0 (SetTheory.app (SetTheory.app (cval iffName ψ) A) B) fun _ =>
          SetTheory.app (SetTheory.app (SetTheory.app (eqVal V (pxψ ψ))
            (univ 0)) A) B) := by
  have hE' : env.find? (Name.anonymous.str "Eq") = some eqA := hE
  have hvalE' : ∀ ψ'' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ'' = eqVal V ψ'' := hvalE
  have hIf' : env.find? (Name.anonymous.str "Iff") =
      some (.indInfo cvI caps) := hIf
  simp only [interpClosed, propextA, interpExpr, Expr.instantiate1, updV,
    Level.eval, Option.getD, hE', hvalE', hIf', eqA,
    ConstantInfo.toConstantVal, hlpI, List.length_cons, List.length_nil,
    reduceIte, Level.substFn_nil]
  simp [interpExpr, Expr.instantiate1, updV, uN, pxψ, iffName,
    Level.substFn_nil,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `propext`'s value inhabits its interpreted pinned type. -/
theorem propext_key {env : Env} (m : EnvModel V env)
    (hE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, m.val eqName ψ' = eqVal V ψ')
    {cvI : ConstantVal} {caps : IndCaps}
    (hIf : env.find? iffName = some (.indInfo cvI caps))
    (hIp : ConstantVal.matchesPin cvI iffA.toConstantVal = true)
    {cvIi : ConstantVal}
    (hIif : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hIip : ConstantVal.matchesPin cvIi iffIntroA.toConstantVal = true)
    {cvIr : ConstantVal} {rules : List RecRule}
    (hIrf : env.find? iffRecName = some (.recInfo cvIr 4 4 rules))
    (hIrp : ConstantVal.matchesPin cvIr iffRecA.toConstantVal = true)
    (ψ : Name → Nat) :
    ∃ T, interpClosed V m.val env ψ propextA.type = some T ∧
      propextVal V ∈ˢ T := by
  have hlpI : cvI.levelParams = [] := (ConstantVal.matchesPin_inv hIp).2
  refine ⟨_, interp_propext_type hE hvalE hIf hlpI, ?_⟩
  show SetTheory.pt ∈ˢ _
  refine pt_mem_pi_zero fun A hA => ⟨SetTheory.pt, ?_⟩
  refine pt_mem_pi_zero fun B hB => ⟨SetTheory.pt, ?_⟩
  refine pt_mem_pi_zero fun w hw => ?_
  have hAB : A = B := iff_forces_eq m hIf hIp hIif hIip hIrf hIrp ψ hA hB hw
  rw [eqVal_app₃ (ψ := pxψ ψ)
    (by rw [pxψ_uN]; exact univ_mem_univ 0) hA hB]
  exact ⟨SetTheory.pt, hAB ▸ pt_mem_eqv_self A⟩

/-! ## `Classical.choice`

The value selects, for each interpreted domain, the global choice
`schoice` of the domain — abstracted over the interpreted `Nonempty α`,
which as a stored `Prop`-valued family is either `{pt}` (when the domain
is inhabited, by the stored `Nonempty.intro`'s membership fact) or `∅`
(when it is not, by the stored `Nonempty.rec`'s membership fact at the
constantly-`∅` motive), so the abstraction's domain can be chosen by a
meta-level case split on inhabitation of the domain.
-/

open Classical in
/-- The set-theoretic value of `Classical.choice` at level `u'`. -/
noncomputable def choiceVal (V : Type u) [SetTheory V] (u' : Nat) : V :=
  SetTheory.lam u' (univ u') fun A =>
    if ∃ x : V, x ∈ˢ A then
      SetTheory.lam u' unitSet fun _ => schoice A
    else
      SetTheory.lam u' SetTheory.empty fun _ => SetTheory.pt

/-- Interpretation of `Nonempty`'s pinned type, computed. -/
theorem interp_nonempty_type {cval : ConstVal V} :
    interpClosed V cval env ψ nonemptyA.toConstantVal.type =
      some (pi 1 (univ (ψ uN)) fun _ => univ 0) := by
  simp only [interpClosed, nonemptyA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD]
  simp [interpExpr, Expr.instantiate1, updV, uN]
  try rfl

/-- The stored `Nonempty` value is a member of the interpreted pinned
type. -/
theorem nonemptyVal_mem (m : EnvModel V env)
    {cvN : ConstantVal} {capsN : IndCaps}
    (hNf : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hNp : ConstantVal.matchesPin cvN nonemptyA.toConstantVal = true)
    (ψ' : Name → Nat) :
    m.val nonemptyName ψ' ∈ˢ pi 1 (univ (ψ' uN)) fun _ => univ 0 := by
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hNf) ψ'
  rw [show (ConstantInfo.indInfo cvN capsN).toConstantVal = cvN from rfl]
    at ht
  rw [interpClosed_matchesPin hNp, interp_nonempty_type] at ht
  obtain rfl := Option.some.inj ht
  have hname : cvN.name = nonemptyName := (ConstantVal.matchesPin_inv hNp).1
  rw [show (ConstantInfo.indInfo cvN capsN).name = cvN.name from rfl,
    hname] at hmem
  exact hmem

/-- The interpreted `Nonempty A` is a truth value. -/
theorem nonemptyVal_app_mem (m : EnvModel V env)
    {cvN : ConstantVal} {capsN : IndCaps}
    (hNf : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hNp : ConstantVal.matchesPin cvN nonemptyA.toConstantVal = true)
    (ψ' : Name → Nat) {A : V} (hA : A ∈ˢ univ (ψ' uN)) :
    SetTheory.app (m.val nonemptyName ψ') A ∈ˢ univ 0 :=
  app_mem (nonemptyVal_mem m hNf hNp ψ') hA (fun _ _ => univ_mem_univ 0)

/-- Interpretation of `Nonempty.intro`'s pinned type, computed. -/
theorem interp_nonemptyIntro_type {cval : ConstVal V}
    {cvN : ConstantVal} {capsN : IndCaps}
    (hNf : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = [uN]) :
    interpClosed V cval env ψ nonemptyIntroA.toConstantVal.type =
      some (pi 0 (univ (ψ uN)) fun A =>
        pi 0 A fun _ => SetTheory.app (cval nonemptyName ψ) A) := by
  have hNf' : env.find? (Name.anonymous.str "Nonempty") =
      some (.indInfo cvN capsN) := hNf
  have hsub : Level.substFn ψ [Name.anonymous.str "u"]
      [Level.param (Name.anonymous.str "u")] = ψ :=
    funext fun _ => Level.substFn_map_param
  simp only [interpClosed, nonemptyIntroA, ConstantInfo.toConstantVal,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD, hNf',
    hlpN, uN, List.length_cons, List.length_nil, reduceIte, hsub]
  simp [interpExpr, Expr.instantiate1, updV, uN, nonemptyName, hsub,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- The stored `Nonempty.intro` value is a member of the interpreted
pinned type. -/
theorem nonemptyIntroVal_mem (m : EnvModel V env)
    {cvN : ConstantVal} {capsN : IndCaps}
    (hNf : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hNp : ConstantVal.matchesPin cvN nonemptyA.toConstantVal = true)
    {cvNi : ConstantVal}
    (hNif : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hNip : ConstantVal.matchesPin cvNi nonemptyIntroA.toConstantVal = true)
    (ψ' : Name → Nat) :
    m.val nonemptyIntroName ψ' ∈ˢ
      pi 0 (univ (ψ' uN)) fun A =>
        pi 0 A fun _ => SetTheory.app (m.val nonemptyName ψ') A := by
  have hlpN : cvN.levelParams = [uN] := (ConstantVal.matchesPin_inv hNp).2
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hNif) ψ'
  rw [show (ConstantInfo.ctorInfo cvNi 1 1).toConstantVal = cvNi from rfl]
    at ht
  rw [interpClosed_matchesPin hNip, interp_nonemptyIntro_type hNf hlpN] at ht
  obtain rfl := Option.some.inj ht
  have hname : cvNi.name = nonemptyIntroName :=
    (ConstantVal.matchesPin_inv hNip).1
  rw [show (ConstantInfo.ctorInfo cvNi 1 1).name = cvNi.name from rfl,
    hname] at hmem
  exact hmem

/-- The interpreted `Nonempty.intro A a` inhabits the interpreted
`Nonempty A`. -/
theorem nonemptyIntroVal_app₂_mem (m : EnvModel V env)
    {cvN : ConstantVal} {capsN : IndCaps}
    (hNf : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hNp : ConstantVal.matchesPin cvN nonemptyA.toConstantVal = true)
    {cvNi : ConstantVal}
    (hNif : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hNip : ConstantVal.matchesPin cvNi nonemptyIntroA.toConstantVal = true)
    (ψ' : Name → Nat) {A a : V} (hA : A ∈ˢ univ (ψ' uN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (m.val nonemptyIntroName ψ') A) a ∈ˢ
      SetTheory.app (m.val nonemptyName ψ') A := by
  have h1 := app_mem (nonemptyIntroVal_mem m hNf hNp hNif hNip ψ') hA
    (fun X hX => pi0_mem_univ0 hX
      (fun _ _ => nonemptyVal_app_mem m hNf hNp ψ' hX))
  exact app_mem h1 ha
    (fun _ _ => nonemptyVal_app_mem m hNf hNp ψ' hA)

/-- Interpretation of `Nonempty.rec`'s pinned type, computed. -/
theorem interp_nonemptyRec_type {cval : ConstVal V}
    {cvN : ConstantVal} {capsN : IndCaps}
    (hNf : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = [uN])
    {cvNi : ConstantVal}
    (hNif : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hlpNi : cvNi.levelParams = [uN]) :
    interpClosed V cval env ψ nonemptyRecA.toConstantVal.type =
      some (pi 0 (univ (ψ uN)) fun A =>
        pi 0 (pi 1 (SetTheory.app (cval nonemptyName ψ) A) fun _ => univ 0)
          fun M =>
          pi 0 (pi 0 A fun a => SetTheory.app M
              (SetTheory.app (SetTheory.app (cval nonemptyIntroName ψ) A) a))
            fun _ =>
            pi 0 (SetTheory.app (cval nonemptyName ψ) A) fun t =>
              SetTheory.app M t) := by
  have hNf' : env.find? (Name.anonymous.str "Nonempty") =
      some (.indInfo cvN capsN) := hNf
  have hNif' : env.find? ((Name.anonymous.str "Nonempty").str "intro") =
      some (.ctorInfo cvNi 1 1) := hNif
  have hsub : Level.substFn ψ [Name.anonymous.str "u"]
      [Level.param (Name.anonymous.str "u")] = ψ :=
    funext fun _ => Level.substFn_map_param
  simp only [interpClosed, nonemptyRecA, ConstantInfo.toConstantVal,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD, hNf',
    hNif', hlpN, hlpNi, uN, List.length_cons, List.length_nil, reduceIte,
    hsub]
  simp [interpExpr, Expr.instantiate1, updV, uN, nonemptyName,
    nonemptyIntroName, hsub,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- The stored `Nonempty.rec` value is a member of the interpreted
pinned type. -/
theorem nonemptyRecVal_mem (m : EnvModel V env)
    {cvN : ConstantVal} {capsN : IndCaps}
    (hNf : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hNp : ConstantVal.matchesPin cvN nonemptyA.toConstantVal = true)
    {cvNi : ConstantVal}
    (hNif : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hNip : ConstantVal.matchesPin cvNi nonemptyIntroA.toConstantVal = true)
    {cvNr : ConstantVal} {rulesN : List RecRule}
    (hNrf : env.find? nonemptyRecName = some (.recInfo cvNr 3 3 rulesN))
    (hNrp : ConstantVal.matchesPin cvNr nonemptyRecA.toConstantVal = true)
    (ψ' : Name → Nat) :
    m.val nonemptyRecName ψ' ∈ˢ
      pi 0 (univ (ψ' uN)) fun A =>
        pi 0 (pi 1 (SetTheory.app (m.val nonemptyName ψ') A)
            fun _ => univ 0) fun M =>
          pi 0 (pi 0 A fun a => SetTheory.app M
              (SetTheory.app (SetTheory.app (m.val nonemptyIntroName ψ') A)
                a)) fun _ =>
            pi 0 (SetTheory.app (m.val nonemptyName ψ') A) fun t =>
              SetTheory.app M t := by
  have hlpN : cvN.levelParams = [uN] := (ConstantVal.matchesPin_inv hNp).2
  have hlpNi : cvNi.levelParams = [uN] :=
    (ConstantVal.matchesPin_inv hNip).2
  obtain ⟨t, ht, hmem⟩ := m.mem_type _ (find?_mem hNrf) ψ'
  rw [show (ConstantInfo.recInfo cvNr 3 3 rulesN).toConstantVal = cvNr
    from rfl] at ht
  rw [interpClosed_matchesPin hNrp,
    interp_nonemptyRec_type hNf hlpN hNif hlpNi] at ht
  obtain rfl := Option.some.inj ht
  have hname : cvNr.name = nonemptyRecName :=
    (ConstantVal.matchesPin_inv hNrp).1
  rw [show (ConstantInfo.recInfo cvNr 3 3 rulesN).name = cvNr.name
    from rfl, hname] at hmem
  exact hmem

/-- A witness of the interpreted `Nonempty A` forces `A` to be
inhabited, through the stored recursor's membership fact at the
constantly-`∅` motive (whose minor premise is vacuous over an empty
`A`). -/
theorem nonemptyVal_forces (m : EnvModel V env)
    {cvN : ConstantVal} {capsN : IndCaps}
    (hNf : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hNp : ConstantVal.matchesPin cvN nonemptyA.toConstantVal = true)
    {cvNi : ConstantVal}
    (hNif : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hNip : ConstantVal.matchesPin cvNi nonemptyIntroA.toConstantVal = true)
    {cvNr : ConstantVal} {rulesN : List RecRule}
    (hNrf : env.find? nonemptyRecName = some (.recInfo cvNr 3 3 rulesN))
    (hNrp : ConstantVal.matchesPin cvNr nonemptyRecA.toConstantVal = true)
    (ψ' : Name → Nat) {A h : V} (hA : A ∈ˢ univ (ψ' uN))
    (hh : h ∈ˢ SetTheory.app (m.val nonemptyName ψ') A) :
    ∃ x, x ∈ˢ A := by
  refine Classical.byContradiction fun hno => ?_
  have hNEu : ∀ X : V, X ∈ˢ univ (ψ' uN) →
      SetTheory.app (m.val nonemptyName ψ') X ∈ˢ univ 0 :=
    fun X hX => nonemptyVal_app_mem m hNf hNp ψ' hX
  have hIntro2 : ∀ X : V, X ∈ˢ univ (ψ' uN) → ∀ a : V, a ∈ˢ X →
      SetTheory.app (SetTheory.app (m.val nonemptyIntroName ψ') X) a ∈ˢ
        SetTheory.app (m.val nonemptyName ψ') X :=
    fun X hX a ha => nonemptyIntroVal_app₂_mem m hNf hNp hNif hNip ψ' hX ha
  -- the constantly-`∅` motive
  have hM : (SetTheory.lam 1 (SetTheory.app (m.val nonemptyName ψ') A)
        fun _ => SetTheory.empty) ∈ˢ
      pi 1 (SetTheory.app (m.val nonemptyName ψ') A) fun _ => univ 0 :=
    lam_mem fun _ _ => empty_mem_univ 0
  -- universe scaffolding for the elimination chain
  have hMS : ∀ X : V, X ∈ˢ univ (ψ' uN) →
      (pi 1 (SetTheory.app (m.val nonemptyName ψ') X) fun _ => univ 0) ∈ˢ
        univ 1 := fun X hX => by
    simpa using pi_mem_univ (u := 0) (v := 1) (B := fun _ => univ 0)
      (hNEu X hX) (fun _ _ => univ_mem_univ 0)
  have hminorU : ∀ X M' : V, X ∈ˢ univ (ψ' uN) →
      M' ∈ˢ (pi 1 (SetTheory.app (m.val nonemptyName ψ') X)
        fun _ => univ 0) →
      (pi 0 X fun a => SetTheory.app M'
        (SetTheory.app (SetTheory.app (m.val nonemptyIntroName ψ') X) a)) ∈ˢ
        univ 0 := by
    intro X M' hX hM'
    exact pi0_mem_univ0 hX (fun a ha =>
      app_mem hM' (hIntro2 X hX a ha) (fun _ _ => univ_mem_univ 0))
  have htail : ∀ X M' : V, X ∈ˢ univ (ψ' uN) →
      M' ∈ˢ (pi 1 (SetTheory.app (m.val nonemptyName ψ') X)
        fun _ => univ 0) →
      (pi 0 (SetTheory.app (m.val nonemptyName ψ') X) fun t =>
        SetTheory.app M' t) ∈ˢ univ 0 := by
    intro X M' hX hM'
    exact pi0_mem_univ0 (hNEu X hX)
      (fun t ht => app_mem hM' ht (fun _ _ => univ_mem_univ 0))
  -- eliminate down the recursor's telescope
  have r1 := app_mem (nonemptyRecVal_mem m hNf hNp hNif hNip hNrf hNrp ψ')
    hA (fun X hX =>
      pi0_mem_univ0 (hMS X hX) fun M' hM' =>
        pi0_mem_univ0 (hminorU X M' hX hM')
          (fun _ _ => htail X M' hX hM'))
  have r2 := app_mem r1 hM (fun M' hM' =>
    pi0_mem_univ0 (hminorU A M' hA hM')
      (fun _ _ => htail A M' hA hM'))
  have hminor : SetTheory.pt ∈ˢ
      pi 0 A fun a => SetTheory.app
        (SetTheory.lam 1 (SetTheory.app (m.val nonemptyName ψ') A)
          fun _ => SetTheory.empty)
        (SetTheory.app (SetTheory.app (m.val nonemptyIntroName ψ') A) a) :=
    pt_mem_pi_zero fun a ha => absurd ⟨a, ha⟩ hno
  have r3 := app_mem r2 hminor (fun _ _ => htail A _ hA hM)
  have r4 := app_mem r3 hh
    (fun t ht => app_mem hM ht (fun _ _ => univ_mem_univ 0))
  rw [app_lam (B := fun _ => univ 0) hh (fun _ _ => empty_mem_univ 0)
    (fun _ _ => univ_mem_univ 0)] at r4
  exact not_mem_empty _ r4

/-- Raw evaluation of `Classical.choice`'s outer binder annotation
(`imax 0 u`). -/
def chA (n : Nat) : Nat := if n = 0 then 0 else Nat.max 0 n

theorem chA_eq (n : Nat) : chA n = n := by
  unfold chA
  by_cases h : n = 0
  · rw [if_pos h, h]
  · rw [if_neg h]
    exact Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.zero_le n, Nat.le_refl n⟩)
      (Nat.le_max_right 0 n)

/-- Interpretation of `Classical.choice`'s pinned type, computed. -/
theorem interp_choice_type {cval : ConstVal V}
    {cvN : ConstantVal} {capsN : IndCaps}
    (hNf : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = [uN]) :
    interpClosed V cval env ψ choiceA.type =
      some (pi (chA (ψ uN)) (univ (ψ uN)) fun A =>
        pi (ψ uN) (SetTheory.app (cval nonemptyName ψ) A) fun _ => A) := by
  have hNf' : env.find? (Name.anonymous.str "Nonempty") =
      some (.indInfo cvN capsN) := hNf
  have hsub : Level.substFn ψ [Name.anonymous.str "u"]
      [Level.param (Name.anonymous.str "u")] = ψ :=
    funext fun _ => Level.substFn_map_param
  simp only [interpClosed, choiceA, interpExpr, Expr.instantiate1, updV,
    Level.eval, Option.getD, hNf', hlpN, uN, ConstantInfo.toConstantVal,
    List.length_cons, List.length_nil, reduceIte, hsub]
  simp [interpExpr, Expr.instantiate1, updV, uN, nonemptyName, hsub, chA,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `Classical.choice`'s value inhabits its interpreted pinned type. -/
theorem choice_key {env : Env} (m : EnvModel V env)
    {cvN : ConstantVal} {capsN : IndCaps}
    (hNf : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hNp : ConstantVal.matchesPin cvN nonemptyA.toConstantVal = true)
    {cvNi : ConstantVal}
    (hNif : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hNip : ConstantVal.matchesPin cvNi nonemptyIntroA.toConstantVal = true)
    {cvNr : ConstantVal} {rulesN : List RecRule}
    (hNrf : env.find? nonemptyRecName = some (.recInfo cvNr 3 3 rulesN))
    (hNrp : ConstantVal.matchesPin cvNr nonemptyRecA.toConstantVal = true)
    (ψ : Name → Nat) :
    ∃ T, interpClosed V m.val env ψ choiceA.type = some T ∧
      choiceVal V (ψ uN) ∈ˢ T := by
  have hlpN : cvN.levelParams = [uN] := (ConstantVal.matchesPin_inv hNp).2
  refine ⟨_, interp_choice_type hNf hlpN, ?_⟩
  rw [chA_eq]
  simp only [choiceVal]
  refine lam_mem (V := V) fun A hA => ?_
  have hNEu : SetTheory.app (m.val nonemptyName ψ) A ∈ˢ univ 0 :=
    nonemptyVal_app_mem m hNf hNp ψ hA
  by_cases hx : ∃ x : V, x ∈ˢ A
  · rw [if_pos hx]
    obtain ⟨x, hxA⟩ := hx
    have hintro := nonemptyIntroVal_app₂_mem m hNf hNp hNif hNip ψ hA hxA
    have hptNE : SetTheory.pt ∈ˢ SetTheory.app (m.val nonemptyName ψ) A := by
      rwa [mem_univ_zero hNEu hintro] at hintro
    have hNEeq : SetTheory.app (m.val nonemptyName ψ) A = unitSet :=
      prop_ext hNEu (unitSet_mem_univ 0) (fun _ => pt_mem_unitSet)
        (fun _ => hptNE)
    rw [hNEeq]
    exact lam_mem fun _ _ => schoice_mem hxA
  · rw [if_neg hx]
    have hNEeq : SetTheory.app (m.val nonemptyName ψ) A =
        SetTheory.empty :=
      prop_ext hNEu (empty_mem_univ 0)
        (fun hpt =>
          absurd (nonemptyVal_forces m hNf hNp hNif hNip hNrf hNrp ψ hA hpt)
            hx)
        (fun hpt => absurd hpt (not_mem_empty _))
    rw [hNEeq]
    exact lam_mem fun y hy => absurd hy (not_mem_empty y)

end Setlec
