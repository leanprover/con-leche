import Setlec.Model.Basis.Util
import Setlec.Model.Basis.Eq.Install

/-!
# `Quot` basis block: interpretation and `hkey` obligations
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-! Raw evaluations of the pinned `Quot` binder annotations (hoisted
for the annotation-tie obligations below). -/

def qtA (u : Nat) : Nat :=
  Nat.max (if Nat.max u 1 = 0 then 0 else Nat.max u (Nat.max u 1)) (u + 1)

def qmR (u : Nat) : Nat := if u = 0 then 0 else u

def qmA (u : Nat) : Nat :=
  if qmR u = 0 then 0
  else Nat.max (if Nat.max u 1 = 0 then 0 else Nat.max u (Nat.max u 1))
    (qmR u)

/-- The level assignment `Eq`'s value sees inside `Quot.lift`'s type
(`Eq` is instantiated at level `v` there). -/
def qlψ (ψ : Name → Nat) : Name → Nat :=
  Level.substFn ψ [uN] [Level.param vN]

def qlQ (u v : Nat) : Nat := if v = 0 then 0 else Nat.max u v

def qlV (u v : Nat) : Nat := if qlQ u v = 0 then 0 else qlQ u v

def qlB (u v : Nat) : Nat :=
  if qlV u v = 0 then 0 else Nat.max (qlQ u v) (qlV u v)

def qlR (u v : Nat) : Nat :=
  if qlB u v = 0 then 0 else Nat.max (v + 1) (qlB u v)

def qlA (u v : Nat) : Nat :=
  if qlR u v = 0 then 0
  else Nat.max (if Nat.max u 1 = 0 then 0 else Nat.max u (Nat.max u 1))
    (qlR u v)

/-! ## Shape facts for the quotient value spaces -/

/-- The relation space `α → α → Prop` lands in `Sort (imax u 2)`'s
evaluation `max u 1`. -/
theorem relSpace_mem_univ {u : Nat} {A : V} (hA : A ∈ˢ univ u) :
    relSpace V u A ∈ˢ univ (Nat.max u 1) := by
  unfold relSpace
  have hin : ∀ x, x ∈ˢ A → (pi 1 A fun _ => univ 0) ∈ˢ univ (Nat.max u 1) := by
    intro x hx
    simpa using pi_mem_univ (u := u) (v := 1) (B := fun _ => univ 0) hA
      (fun _ _ => univ_mem_univ 0)
  have hmem := pi_mem_univ (u := u) (v := Nat.max u 1) hA hin
  rw [if_neg (max_ne_zero_r' (by decide))] at hmem
  rwa [max_absorb_l'] at hmem

/-- The fibre family of `Quot`'s value, in its universe. -/
theorem quot_fibre_mem {u : Nat} {A : V} (hA : A ∈ˢ univ u) :
    (pi (u + 1) (relSpace V u A) fun _ => univ u) ∈ˢ univ (u + 1) := by
  have hmem := pi_mem_univ (u := Nat.max u 1) (v := u + 1)
    (B := fun _ => univ u) (relSpace_mem_univ hA)
    (fun _ _ => univ_mem_univ u)
  rw [if_neg (Nat.succ_ne_zero u)] at hmem
  rwa [show Nat.max (Nat.max u 1) (u + 1) = u + 1 from
    Nat.le_antisymm
      (Nat.max_le.mpr ⟨Nat.max_le.mpr
        ⟨Nat.le_succ u, Nat.succ_le_succ (Nat.zero_le u)⟩, Nat.le_refl _⟩)
      (Nat.le_max_right _ _)] at hmem

/-- The innermost fibre family of `Quot.mk`'s value, in its universe. -/
theorem mkA_fibre_mem {u : Nat} {A R : V} (hA : A ∈ˢ univ u) :
    (pi u A fun _ => quotSet u A R) ∈ˢ univ u := by
  have hmem := pi_mem_univ (u := u) (v := u) (B := fun _ => quotSet u A R)
    hA (fun _ _ => quotSet_mem_univ hA)
  by_cases hu : u = 0
  · simpa [hu] using hmem
  · simpa [if_neg hu, Nat.max_self] using hmem

/-- The fibre family of `Quot.mk`'s value, in its universe. -/
theorem mk_fibre_mem {u : Nat} {A : V} (hA : A ∈ˢ univ u) :
    (pi u (relSpace V u A) fun R => pi u A fun _ => quotSet u A R) ∈ˢ
      univ u := by
  have hmem := pi_mem_univ (u := Nat.max u 1) (v := u)
    (B := fun R => pi u A fun _ => quotSet u A R) (relSpace_mem_univ hA)
    (fun R _ => mkA_fibre_mem hA)
  by_cases hu : u = 0
  · simpa [hu] using hmem
  · rw [if_neg hu, show Nat.max (Nat.max u 1) u = u from
      Nat.le_antisymm
        (Nat.max_le.mpr ⟨Nat.max_le.mpr
          ⟨Nat.le_refl u, Nat.one_le_iff_ne_zero.mpr hu⟩, Nat.le_refl u⟩)
        (Nat.le_max_right _ _)] at hmem
    exact hmem

/-! ## Application lemmas for `quotVal` and `quotMkVal` -/

/-- `Quot`'s value is a member of its pi-type (the shape app reasoning
uses). -/
theorem quotVal_mem :
    (quotVal V ψ : V) ∈ˢ pi (ψ uN + 1) (univ (ψ uN)) (fun A =>
      pi (ψ uN + 1) (relSpace V (ψ uN) A) fun _ => univ (ψ uN)) := by
  simp only [quotVal]
  refine lam_mem (V := V) (B := fun A =>
    pi (ψ uN + 1) (relSpace V (ψ uN) A) fun _ => univ (ψ uN)) fun A hA => ?_
  exact lam_mem (V := V) (B := fun _ => univ (ψ uN))
    fun R _ => quotSet_mem_univ hA

/-- Applying `Quot`'s value to a domain computes to the lam over
relations. -/
theorem quotVal_app {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (quotVal V ψ) A =
      SetTheory.lam (ψ uN + 1) (relSpace V (ψ uN) A) fun R =>
        quotSet (ψ uN) A R := by
  simp only [quotVal]
  exact app_lam (B := fun X =>
      pi (ψ uN + 1) (relSpace V (ψ uN) X) fun _ => univ (ψ uN)) hA
    (fun X hX => lam_mem (V := V) (B := fun _ => univ (ψ uN))
      fun R _ => quotSet_mem_univ hX)
    (fun X hX => quot_fibre_mem hX)

theorem quotVal_app_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (quotVal V ψ) A ∈ˢ
      pi (ψ uN + 1) (relSpace V (ψ uN) A) (fun _ => univ (ψ uN)) := by
  rw [quotVal_app hA]
  exact lam_mem (V := V) (B := fun _ => univ (ψ uN))
    fun R _ => quotSet_mem_univ hA

/-- The full application of `Quot`'s value is the quotient set. -/
theorem quotVal_app₂ {A R : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) :
    SetTheory.app (SetTheory.app (quotVal V ψ) A) R =
      quotSet (ψ uN) A R := by
  rw [quotVal_app hA]
  exact app_lam (B := fun _ => univ (ψ uN)) hR
    (fun R' _ => quotSet_mem_univ hA)
    (fun R' _ => univ_mem_univ (ψ uN))

theorem quotVal_app₂_mem {A R : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) :
    SetTheory.app (SetTheory.app (quotVal V ψ) A) R ∈ˢ univ (ψ uN) := by
  rw [quotVal_app₂ hA hR]
  exact quotSet_mem_univ hA

/-- `Quot.mk`'s value is a member of its pi-type. -/
theorem quotMkVal_mem :
    (quotMkVal V ψ : V) ∈ˢ pi (ψ uN) (univ (ψ uN)) (fun A =>
      pi (ψ uN) (relSpace V (ψ uN) A) fun R =>
        pi (ψ uN) A fun _ => quotSet (ψ uN) A R) := by
  simp only [quotMkVal]
  refine lam_mem (V := V) (B := fun A =>
    pi (ψ uN) (relSpace V (ψ uN) A) fun R =>
      pi (ψ uN) A fun _ => quotSet (ψ uN) A R) fun A hA => ?_
  refine lam_mem (V := V) (B := fun R =>
    pi (ψ uN) A fun _ => quotSet (ψ uN) A R) fun R _ => ?_
  exact lam_mem (V := V) (B := fun _ => quotSet (ψ uN) A R)
    fun a ha => quotClass_mem ha

/-- Applying `Quot.mk`'s value to a domain. -/
theorem quotMkVal_app {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (quotMkVal V ψ) A =
      SetTheory.lam (ψ uN) (relSpace V (ψ uN) A) fun R =>
        SetTheory.lam (ψ uN) A fun a => quotClass (ψ uN) A R a := by
  simp only [quotMkVal]
  exact app_lam (B := fun X =>
      pi (ψ uN) (relSpace V (ψ uN) X) fun R =>
        pi (ψ uN) X fun _ => quotSet (ψ uN) X R) hA
    (fun X hX => lam_mem (V := V) (B := fun R =>
        pi (ψ uN) X fun _ => quotSet (ψ uN) X R)
      fun R _ => lam_mem (V := V) (B := fun _ => quotSet (ψ uN) X R)
        fun a ha => quotClass_mem ha)
    (fun X hX => mk_fibre_mem hX)

theorem quotMkVal_app_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (quotMkVal V ψ) A ∈ˢ
      pi (ψ uN) (relSpace V (ψ uN) A) (fun R =>
        pi (ψ uN) A fun _ => quotSet (ψ uN) A R) := by
  rw [quotMkVal_app hA]
  exact lam_mem (V := V) (B := fun R =>
      pi (ψ uN) A fun _ => quotSet (ψ uN) A R)
    fun R _ => lam_mem (V := V) (B := fun _ => quotSet (ψ uN) A R)
      fun a ha => quotClass_mem ha

/-- Applying `Quot.mk`'s value to a domain and a relation. -/
theorem quotMkVal_app₂ {A R : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) :
    SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R =
      SetTheory.lam (ψ uN) A fun a => quotClass (ψ uN) A R a := by
  rw [quotMkVal_app hA]
  exact app_lam (B := fun R' => pi (ψ uN) A fun _ => quotSet (ψ uN) A R')
    hR
    (fun R' _ => lam_mem (V := V) (B := fun _ => quotSet (ψ uN) A R')
      fun a ha => quotClass_mem ha)
    (fun R' _ => mkA_fibre_mem hA)

theorem quotMkVal_app₂_mem {A R : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) :
    SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R ∈ˢ
      pi (ψ uN) A (fun _ => quotSet (ψ uN) A R) := by
  rw [quotMkVal_app₂ hA hR]
  exact lam_mem (V := V) (B := fun _ => quotSet (ψ uN) A R)
    fun a ha => quotClass_mem ha

/-- The full application of `Quot.mk`'s value is the class. -/
theorem quotMkVal_app₃ {A R a : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R) a =
      quotClass (ψ uN) A R a := by
  rw [quotMkVal_app₂ hA hR]
  exact app_lam (B := fun _ => quotSet (ψ uN) A R) ha
    (fun a' ha' => quotClass_mem ha')
    (fun _ _ => quotSet_mem_univ hA)

theorem quotMkVal_app₃_mem {A R a : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R) a ∈ˢ
      quotSet (ψ uN) A R := by
  rw [quotMkVal_app₃ hA hR ha]
  exact quotClass_mem ha

/-! ## `Quot` -/

/-- The raw evaluation of `Quot`'s outer binder annotation. -/

theorem qtA_eq (u : Nat) : qtA u = u + 1 := by
  unfold qtA
  rw [if_neg (max_ne_zero_r' (by decide))]
  exact Nat.le_antisymm
    (Nat.max_le.mpr ⟨Nat.max_le.mpr
      ⟨Nat.le_succ u, Nat.max_le.mpr
        ⟨Nat.le_succ u, Nat.succ_le_succ (Nat.zero_le u)⟩⟩, Nat.le_refl _⟩)
    (Nat.le_max_right _ _)

/-- Interpretation of `Quot`'s pinned type, computed. -/
theorem interp_quot_type {cval : ConstVal V} :
    interpClosed V cval env ψ quotA.toConstantVal.type =
      some (pi (qtA (ψ uN)) (univ (ψ uN)) fun A =>
        pi (ψ uN + 1) (relSpace V (ψ uN) A) fun _ => univ (ψ uN)) := by
  simp only [interpClosed, quotA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD]
  simp [interpExpr, Expr.instantiate1, updV, uN, relSpace,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `Quot`'s value inhabits its type. -/
theorem quot_key {cval : ConstVal V} :
    ∃ T, interpClosed V cval env ψ quotA.toConstantVal.type = some T ∧
      quotVal V ψ ∈ˢ T := by
  refine ⟨_, interp_quot_type, ?_⟩
  rw [qtA_eq]
  exact quotVal_mem

/-- `Quot`'s type carries truthful annotations. -/
theorem annotOk_quot_type {cval : ConstVal V} :
    AnnotOk V cval env ψ 0 (rho0 V) quotA.toConstantVal.type := by
  simp only [quotA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ψ uN + 1, ?_⟩
  refine ⟨?_, ?_⟩
  · first
      | (rintro v ⟨rfl⟩; exact fun z hz => hz)
      | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
      | (rintro v ⟨rfl⟩
         intro z hz
         refine univ_mono ?_ z hz
         simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
         by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · -- the opened body `(α → α → Prop) → Sort u`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, ψ uN + 1, ?_⟩
    · -- the relation space `α → α → Prop`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, Nat.max (ψ uN) 1, ?_⟩
      refine ⟨?_, ?_⟩
      · first
          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
          | (rintro v ⟨rfl⟩
             intro z hz
             refine univ_mono ?_ z hz
             simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
      intro x Sx hSx hxmem
      have hSx' : Sx = A := by
        simp only [interpExpr, updV, Expr.instantiate1, reduceIte,
          Option.some.injEq] at hSx
        exact hSx.symm
      rw [hSx'] at hxmem
      refine ⟨?_, ?_⟩
      · -- `α → Prop`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨trivial, 1, ?_⟩
        refine ⟨?_, ?_⟩
        · first
            | (rintro v ⟨rfl⟩; exact fun z hz => hz)
            | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
            | (rintro v ⟨rfl⟩
               intro z hz
               refine univ_mono ?_ z hz
               simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
               by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
        intro y Sy hSy hymem
        refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
        refine ⟨univ 0, ?_, ?_⟩
        · simp [Expr.instantiate1, interpExpr, Level.eval]
        · exact univ_mem_univ 0
      · refine ⟨pi 1 A (fun _ => univ 0), ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
        · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
            hAmem (fun _ _ => univ_mem_univ 0)
    · refine ⟨?_, ?_⟩
      · first
          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
          | (rintro v ⟨rfl⟩
             intro z hz
             refine univ_mono ?_ z hz
             simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
      intro R SR hSR hRmem
      refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
      refine ⟨univ (ψ uN), ?_, ?_⟩
      · simp [Expr.instantiate1, interpExpr, Level.eval, uN]
      · exact univ_mem_univ (ψ uN)
  · refine ⟨pi (ψ uN + 1) (relSpace V (ψ uN) A) (fun _ => univ (ψ uN)),
      ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, Level.eval, uN, relSpace,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · exact quot_fibre_mem (V := V) hAmem

/-! ## `Quot.mk` -/

/-! Raw evaluations of `Quot.mk`'s binder annotations (in the forms the
interpretation's `simp` normalization leaves). -/


theorem qmR_eq (u : Nat) : qmR u = u := by
  unfold qmR
  by_cases h : u = 0
  · rw [if_pos h, h]
  · rw [if_neg h]

theorem qmA_eq (u : Nat) : qmA u = u := by
  unfold qmA
  rw [qmR_eq]
  by_cases h : u = 0
  · simp [h]
  · rw [if_neg h, if_neg (max_ne_zero_r' (by decide))]
    exact Nat.le_antisymm
      (Nat.max_le.mpr ⟨Nat.max_le.mpr
        ⟨Nat.le_refl u, Nat.max_le.mpr
          ⟨Nat.le_refl u, Nat.one_le_iff_ne_zero.mpr h⟩⟩, Nat.le_refl u⟩)
      (Nat.le_max_right _ _)

/-- Interpretation of `Quot.mk`'s pinned type, computed. -/
theorem interp_quotMk_type {cval : ConstVal V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ') :
    interpClosed V cval env ψ quotMkA.toConstantVal.type =
      some (pi (qmA (ψ uN)) (univ (ψ uN)) fun A =>
        pi (qmR (ψ uN)) (relSpace V (ψ uN) A) fun R =>
          pi (ψ uN) A fun _ =>
            SetTheory.app (SetTheory.app (quotVal V ψ) A) R) := by
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA := hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  simp only [interpClosed, quotMkA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindQ', hvalQ', quotA, List.length_cons, List.length_nil, reduceIte,
    Level.substFn]
  simp [interpExpr, Expr.instantiate1, updV, uN, relSpace,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `Quot.mk`'s value inhabits its type. -/
theorem quotMk_key {cval : ConstVal V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ') :
    ∃ T, interpClosed V cval env ψ quotMkA.toConstantVal.type = some T ∧
      quotMkVal V ψ ∈ˢ T := by
  refine ⟨_, interp_quotMk_type hfindQ hvalQ, ?_⟩
  rw [qmA_eq, qmR_eq]
  simp only [quotMkVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun R hR => ?_
  refine lam_mem (V := V) fun a ha => ?_
  rw [quotVal_app₂ hA hR]
  exact quotClass_mem ha

/-- `Quot.mk`'s type carries truthful annotations. -/
theorem annotOk_quotMk_type {cval : ConstVal V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) quotMkA.toConstantVal.type := by
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA := hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  simp only [quotMkA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ψ uN, ?_⟩
  refine ⟨?_, ?_⟩
  · first
      | (rintro v ⟨rfl⟩; exact fun z hz => hz)
      | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
      | (rintro v ⟨rfl⟩
         intro z hz
         refine univ_mono ?_ z hz
         simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
         by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · -- the opened body `(r : α → α → Prop) → (a : α) → Quot α r`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, ψ uN, ?_⟩
    · -- the relation space `α → α → Prop`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, Nat.max (ψ uN) 1, ?_⟩
      refine ⟨?_, ?_⟩
      · first
          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
          | (rintro v ⟨rfl⟩
             intro z hz
             refine univ_mono ?_ z hz
             simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
      intro x Sx hSx hxmem
      have hSx' : Sx = A := by
        simp only [interpExpr, updV, Expr.instantiate1, reduceIte,
          Option.some.injEq] at hSx
        exact hSx.symm
      rw [hSx'] at hxmem
      refine ⟨?_, ?_⟩
      · try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨trivial, 1, ?_⟩
        refine ⟨?_, ?_⟩
        · first
            | (rintro v ⟨rfl⟩; exact fun z hz => hz)
            | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
            | (rintro v ⟨rfl⟩
               intro z hz
               refine univ_mono ?_ z hz
               simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
               by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
        intro y Sy hSy hymem
        refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
        refine ⟨univ 0, ?_, ?_⟩
        · simp [Expr.instantiate1, interpExpr, Level.eval]
        · exact univ_mem_univ 0
      · refine ⟨pi 1 A (fun _ => univ 0), ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
        · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
            hAmem (fun _ _ => univ_mem_univ 0)
    · refine ⟨?_, ?_⟩
      · first
          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
          | (rintro v ⟨rfl⟩
             intro z hz
             refine univ_mono ?_ z hz
             simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
      intro R SR hSR hRmem
      simp [interpExpr, Expr.instantiate1, updV, Level.eval,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSR
      subst hSR
      have hRmem' : R ∈ˢ relSpace V (ψ uN) A := hRmem
      refine ⟨?_, ?_⟩
      · -- the opened `(a : α) → Quot α r`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨trivial, ψ uN, ?_⟩
        refine ⟨?_, ?_⟩
        · first
            | (rintro v ⟨rfl⟩; exact fun z hz => hz)
            | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
            | (rintro v ⟨rfl⟩
               intro z hz
               refine univ_mono ?_ z hz
               simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
               by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
        intro a Sa hSa hamem
        simp [interpExpr, Expr.instantiate1, updV] at hSa
        subst hSa
        refine ⟨?_, ?_⟩
        · -- the body `Quot α r` (two app clauses)
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
              (by simp [Expr.instantiate1, AnnotOk]),
              quotVal V ψ, A, ψ uN + 1, univ (ψ uN),
              (fun X => pi (ψ uN + 1) (relSpace V (ψ uN) X) fun _ =>
                univ (ψ uN)),
              ?_, ?_, quotVal_mem, hAmem, fun X hX => quot_fibre_mem hX⟩,
            (by simp [Expr.instantiate1, AnnotOk]),
            SetTheory.app (quotVal V ψ) A, R, ψ uN + 1,
            relSpace V (ψ uN) A, (fun _ => univ (ψ uN)),
            ?_, ?_, quotVal_app_mem hAmem, hRmem',
            fun _ _ => univ_mem_univ (ψ uN)⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
              quotA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
          · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
              quotA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
        · -- fibre-universe of the `a` binder (annotation `u`)
          refine ⟨SetTheory.app (SetTheory.app (quotVal V ψ) A) R, ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
              quotA, ConstantInfo.toConstantVal]
            try rfl
          · exact quotVal_app₂_mem hAmem hRmem'
      · -- fibre-universe of the `r` binder (annotation `imax u u`)
        refine ⟨pi (ψ uN) A (fun _ =>
          SetTheory.app (SetTheory.app (quotVal V ψ) A) R), ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
            quotA, ConstantInfo.toConstantVal, Level.eval, uN,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · simp only [quotVal_app₂ hAmem hRmem']
          exact mkA_fibre_mem hAmem
  · -- fibre-universe of the `α` binder
    refine ⟨pi (qmR (ψ uN)) (relSpace V (ψ uN) A) (fun R =>
      pi (ψ uN) A fun _ =>
        SetTheory.app (SetTheory.app (quotVal V ψ) A) R), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
        quotA, ConstantInfo.toConstantVal, Level.eval, uN, relSpace, qmR,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · have hfib : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
          (pi (ψ uN) A fun _ =>
            SetTheory.app (SetTheory.app (quotVal V ψ) A) R') ∈ˢ
            univ (ψ uN) := by
        intro R' hR'
        simp only [quotVal_app₂ hAmem hR']
        exact mkA_fibre_mem hAmem
      have hmem := pi_mem_univ (u := Nat.max (ψ uN) 1) (v := ψ uN)
        (relSpace_mem_univ hAmem) hfib
      by_cases hu : ψ uN = 0
      · simpa [hu] using hmem
      · rw [if_neg hu, show Nat.max (Nat.max (ψ uN) 1) (ψ uN) = ψ uN from
          Nat.le_antisymm
            (Nat.max_le.mpr ⟨Nat.max_le.mpr
              ⟨Nat.le_refl _, Nat.one_le_iff_ne_zero.mpr hu⟩,
              Nat.le_refl _⟩)
            (Nat.le_max_right _ _)] at hmem
        exact hmem

/-! ## `Quot.lift` -/


theorem qlV_eq (u v : Nat) : qlV u v = qlQ u v := by
  unfold qlV
  by_cases h : qlQ u v = 0
  · rw [if_pos h, h]
  · rw [if_neg h]

theorem qlB_eq (u v : Nat) : qlB u v = qlQ u v := by
  unfold qlB
  rw [qlV_eq]
  by_cases h : qlQ u v = 0
  · simp [h]
  · rw [if_neg h]
    exact Nat.max_self _

theorem qlR_eq (u v : Nat) :
    qlR u v = if v = 0 then 0 else Nat.max (v + 1) (Nat.max u v) := by
  unfold qlR
  rw [qlB_eq]
  unfold qlQ
  by_cases hv : v = 0
  · simp [hv]
  · simp [hv, max_ne_zero_r' hv]

theorem qlA_eq (u v : Nat) :
    qlA u v =
      if (if v = 0 then 0 else Nat.max (v + 1) (Nat.max u v)) = 0 then 0
      else Nat.max (Nat.max u 1)
        (if v = 0 then 0 else Nat.max (v + 1) (Nat.max u v)) := by
  unfold qlA
  rw [qlR_eq, if_neg (max_ne_zero_r' (by decide) : Nat.max u 1 ≠ 0),
    max_absorb_l']

/-- Iterated application of a member of the relation space is a truth
value. -/
theorem relSpace_app₂_mem {A R a b : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) (ha : a ∈ˢ A) (hb : b ∈ˢ A) :
    SetTheory.app (SetTheory.app R a) b ∈ˢ univ 0 := by
  have h1 : SetTheory.app R a ∈ˢ pi 1 A (fun _ => univ 0) :=
    app_mem hR ha (fun x hx =>
      pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0) hA
        (fun _ _ => univ_mem_univ 0))
  exact app_mem h1 hb (fun _ _ => univ_mem_univ 0)

/-- A member of the interpreted invariance space witnesses that `f` is
constant on related elements (the premise of `quotLift_mem`). -/
theorem quotInv_invariant {A R f h : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) (hh : h ∈ˢ quotInvSpace V A R f) :
    ∀ a b, a ∈ˢ A → b ∈ˢ A →
      (∃ w, w ∈ˢ SetTheory.app (SetTheory.app R a) b) →
      SetTheory.app f a = SetTheory.app f b := by
  intro a b ha hb hex
  obtain ⟨w, hw⟩ := hex
  have h1 : SetTheory.app h a ∈ˢ pi 0 A (fun b' =>
      pi 0 (SetTheory.app (SetTheory.app R a) b') fun _ =>
        eqv (SetTheory.app f a) (SetTheory.app f b')) := by
    refine app_mem (v := 0) hh ha ?_
    intro x hx
    exact pi_mem_univ (u := ψ uN) (v := 0) hA (fun b' hb' =>
      pi_mem_univ (u := 0) (v := 0)
        (B := fun _ => eqv (SetTheory.app f x) (SetTheory.app f b'))
        (relSpace_app₂_mem hA hR hx hb') (fun _ _ => eqv_mem_univ _ _))
  have h2 : SetTheory.app (SetTheory.app h a) b ∈ˢ
      pi 0 (SetTheory.app (SetTheory.app R a) b) fun _ =>
        eqv (SetTheory.app f a) (SetTheory.app f b) := by
    refine app_mem h1 hb ?_
    intro x hx
    exact pi_mem_univ (u := 0) (v := 0)
      (B := fun _ => eqv (SetTheory.app f a) (SetTheory.app f x))
      (relSpace_app₂_mem hA hR ha hx) (fun _ _ => eqv_mem_univ _ _)
  have h3 : SetTheory.app (SetTheory.app (SetTheory.app h a) b) w ∈ˢ
      eqv (SetTheory.app f a) (SetTheory.app f b) :=
    app_mem h2 hw (fun _ _ => eqv_mem_univ _ _)
  exact mem_eqv h3

/-- Interpretation of `Quot.lift`'s pinned type, computed. -/
theorem interp_quotLift_type {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ') :
    interpClosed V cval env ψ quotLiftA.toConstantVal.type =
      some (pi (qlA (ψ uN) (ψ vN)) (univ (ψ uN)) fun A =>
        pi (qlR (ψ uN) (ψ vN)) (relSpace V (ψ uN) A) fun R =>
          pi (qlB (ψ uN) (ψ vN)) (univ (ψ vN)) fun B =>
            pi (qlV (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B) fun f =>
              pi (qlQ (ψ uN) (ψ vN))
                (pi 0 A fun a => pi 0 A fun b =>
                  pi 0 (SetTheory.app (SetTheory.app R a) b) fun _ =>
                    SetTheory.app (SetTheory.app
                      (SetTheory.app (eqVal V (qlψ ψ)) B)
                      (SetTheory.app f a)) (SetTheory.app f b)) fun _ =>
                pi (ψ vN) (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
                  fun _ => B) := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA := hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  simp only [interpClosed, quotLiftA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindE', hvalE', hfindQ', hvalQ', eqA, quotA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, Expr.instantiate1, updV, uN, vN, relSpace,
    qlA, qlR, qlB, qlV, qlQ, qlψ,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `Quot.lift`'s value inhabits its type (`quotLift_mem` with the
invariance premise from the interpreted hypothesis space). -/
theorem quotLift_key {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ') :
    ∃ T, interpClosed V cval env ψ quotLiftA.toConstantVal.type = some T ∧
      quotLiftVal V ψ ∈ˢ T := by
  refine ⟨_, interp_quotLift_type hfindE hvalE hfindQ hvalQ, ?_⟩
  rw [qlA_eq, qlR_eq, qlB_eq, qlV_eq]
  simp only [qlQ, quotLiftVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun R hR => ?_
  refine lam_mem (V := V) fun B hB => ?_
  refine lam_mem (V := V) fun f hf => ?_
  have hInv : (pi 0 A fun a => pi 0 A fun b =>
      pi 0 (SetTheory.app (SetTheory.app R a) b) fun _ =>
        SetTheory.app (SetTheory.app (SetTheory.app (eqVal V (qlψ ψ)) B)
          (SetTheory.app f a)) (SetTheory.app f b)) =
      quotInvSpace V A R f := by
    unfold quotInvSpace
    refine pi_congr fun a ha => ?_
    refine pi_congr fun b hb => ?_
    refine pi_congr fun w hw => ?_
    rw [eqVal_app₃ (ψ := qlψ ψ) hB
      (app_mem hf ha (fun _ _ => hB)) (app_mem hf hb (fun _ _ => hB))]
  rw [hInv]
  refine lam_mem (V := V) fun h hh => ?_
  rw [quotVal_app₂ hA hR]
  refine lam_mem (V := V) fun q hq => ?_
  have hlift := quotLift_mem (u := ψ uN) (v := ψ vN) (R := R) hA hf
    (quotInv_invariant hA hR hh)
  exact app_mem hlift hq (fun _ _ => hB)

/-- `Quot.lift`'s type carries truthful annotations. -/
theorem annotOk_quotLift_type {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) quotLiftA.toConstantVal.type := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA := hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  simp only [quotLiftA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, qlA (ψ uN) (ψ vN), ?_⟩
  refine ⟨?_, ?_⟩
  · first
      | (rintro v ⟨rfl⟩; exact fun z hz => hz)
      | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
      | (rintro v ⟨rfl⟩
         intro z hz
         refine univ_mono ?_ z hz
         simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
         by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  -- the telescope-suffix universe facts, parametric in the point
  have hQB : ∀ R', R' ∈ˢ relSpace V (ψ uN) A → ∀ X, X ∈ˢ univ (ψ vN) →
      (pi (ψ vN) (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
        fun _ => X) ∈ˢ univ (qlQ (ψ uN) (ψ vN)) := by
    intro R' hR' X hX
    rw [quotVal_app₂ hAmem hR']
    exact pi_mem_univ (u := ψ uN) (v := ψ vN) (quotSet_mem_univ hAmem)
      (fun _ _ => hX)
  have hfSpace : ∀ X, X ∈ˢ univ (ψ vN) →
      (pi (ψ vN) A fun _ => X) ∈ˢ univ (qlQ (ψ uN) (ψ vN)) :=
    fun X hX => pi_mem_univ (u := ψ uN) (v := ψ vN) hAmem (fun _ _ => hX)
  have hDom3 : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      ∀ B', B' ∈ˢ univ (ψ vN) →
      ∀ f', f' ∈ˢ pi (ψ vN) A (fun _ => B') →
      ∀ a' b', a' ∈ˢ A → b' ∈ˢ A →
      (pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
        SetTheory.app (SetTheory.app (SetTheory.app (eqVal V (qlψ ψ)) B')
          (SetTheory.app f' a')) (SetTheory.app f' b')) ∈ˢ univ 0 := by
    intro R' hR' B' hB' f' hf' a' b' ha' hb'
    simp only [eqVal_app₃ (ψ := qlψ ψ) hB'
      (app_mem hf' ha' (fun _ _ => hB')) (app_mem hf' hb' (fun _ _ => hB'))]
    exact pi_mem_univ (u := 0) (v := 0)
      (relSpace_app₂_mem hAmem hR' ha' hb') (fun _ _ => eqv_mem_univ _ _)
  have hDom2 : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      ∀ B', B' ∈ˢ univ (ψ vN) →
      ∀ f', f' ∈ˢ pi (ψ vN) A (fun _ => B') →
      ∀ a', a' ∈ˢ A →
      (pi 0 A fun b' =>
        pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
          SetTheory.app (SetTheory.app (SetTheory.app (eqVal V (qlψ ψ)) B')
            (SetTheory.app f' a')) (SetTheory.app f' b')) ∈ˢ univ 0 := by
    intro R' hR' B' hB' f' hf' a' ha'
    exact pi_mem_univ (u := ψ uN) (v := 0) hAmem
      (fun b' hb' => hDom3 R' hR' B' hB' f' hf' a' b' ha' hb')
  have hDomMem : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      ∀ B', B' ∈ˢ univ (ψ vN) →
      ∀ f', f' ∈ˢ pi (ψ vN) A (fun _ => B') →
      (pi 0 A fun a' => pi 0 A fun b' =>
        pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
          SetTheory.app (SetTheory.app (SetTheory.app (eqVal V (qlψ ψ)) B')
            (SetTheory.app f' a')) (SetTheory.app f' b')) ∈ˢ univ 0 := by
    intro R' hR' B' hB' f' hf'
    exact pi_mem_univ (u := ψ uN) (v := 0) hAmem
      (fun a' ha' => hDom2 R' hR' B' hB' f' hf' a' ha')
  have hT4 : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      ∀ B', B' ∈ˢ univ (ψ vN) →
      ∀ f', f' ∈ˢ pi (ψ vN) A (fun _ => B') →
      (pi (qlQ (ψ uN) (ψ vN))
        (pi 0 A fun a' => pi 0 A fun b' =>
          pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
            SetTheory.app (SetTheory.app
              (SetTheory.app (eqVal V (qlψ ψ)) B')
              (SetTheory.app f' a')) (SetTheory.app f' b')) fun _ =>
        pi (ψ vN) (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
          fun _ => B') ∈ˢ univ (qlV (ψ uN) (ψ vN)) := by
    intro R' hR' B' hB' f' hf'
    exact pi_mem_univ (u := 0) (v := qlQ (ψ uN) (ψ vN))
      (hDomMem R' hR' B' hB' f' hf') (fun _ _ => hQB R' hR' B' hB')
  have hT3 : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      ∀ B', B' ∈ˢ univ (ψ vN) →
      (pi (qlV (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B') fun f' =>
        pi (qlQ (ψ uN) (ψ vN))
          (pi 0 A fun a' => pi 0 A fun b' =>
            pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
              SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V (qlψ ψ)) B')
                (SetTheory.app f' a')) (SetTheory.app f' b')) fun _ =>
          pi (ψ vN) (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
            fun _ => B') ∈ˢ univ (qlB (ψ uN) (ψ vN)) := by
    intro R' hR' B' hB'
    exact pi_mem_univ (u := qlQ (ψ uN) (ψ vN)) (v := qlV (ψ uN) (ψ vN))
      (hfSpace B' hB') (fun f' hf' => hT4 R' hR' B' hB' f' hf')
  have hT2 : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      (pi (qlB (ψ uN) (ψ vN)) (univ (ψ vN)) fun B' =>
        pi (qlV (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B') fun f' =>
          pi (qlQ (ψ uN) (ψ vN))
            (pi 0 A fun a' => pi 0 A fun b' =>
              pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
                SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V (qlψ ψ)) B')
                  (SetTheory.app f' a')) (SetTheory.app f' b')) fun _ =>
            pi (ψ vN) (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
              fun _ => B') ∈ˢ univ (qlR (ψ uN) (ψ vN)) := by
    intro R' hR'
    exact pi_mem_univ (u := ψ vN + 1) (v := qlB (ψ uN) (ψ vN))
      (univ_mem_univ (ψ vN)) (fun B' hB' => hT3 R' hR' B' hB')
  have hT1 : (pi (qlR (ψ uN) (ψ vN)) (relSpace V (ψ uN) A) fun R' =>
      pi (qlB (ψ uN) (ψ vN)) (univ (ψ vN)) fun B' =>
        pi (qlV (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B') fun f' =>
          pi (qlQ (ψ uN) (ψ vN))
            (pi 0 A fun a' => pi 0 A fun b' =>
              pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
                SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V (qlψ ψ)) B')
                  (SetTheory.app f' a')) (SetTheory.app f' b')) fun _ =>
            pi (ψ vN) (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
              fun _ => B') ∈ˢ univ (qlA (ψ uN) (ψ vN)) := by
    have hmem := pi_mem_univ (u := Nat.max (ψ uN) 1)
      (v := qlR (ψ uN) (ψ vN)) (relSpace_mem_univ hAmem)
      (fun R' hR' => hT2 R' hR')
    unfold qlA
    rw [if_neg (max_ne_zero_r' (by decide) : Nat.max (ψ uN) 1 ≠ 0),
      max_absorb_l']
    exact hmem
  refine ⟨?_, ?_⟩
  · -- the opened `∀ {r}, …`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, qlR (ψ uN) (ψ vN), ?_⟩
    · -- the relation space `α → α → Prop`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, Nat.max (ψ uN) 1, ?_⟩
      refine ⟨?_, ?_⟩
      · first
          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
          | (rintro v ⟨rfl⟩
             intro z hz
             refine univ_mono ?_ z hz
             simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
      intro x Sx hSx hxmem
      have hSx' : Sx = A := by
        simp only [interpExpr, updV, Expr.instantiate1, reduceIte,
          Option.some.injEq] at hSx
        exact hSx.symm
      rw [hSx'] at hxmem
      refine ⟨?_, ?_⟩
      · try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨trivial, 1, ?_⟩
        refine ⟨?_, ?_⟩
        · first
            | (rintro v ⟨rfl⟩; exact fun z hz => hz)
            | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
            | (rintro v ⟨rfl⟩
               intro z hz
               refine univ_mono ?_ z hz
               simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
               by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
        intro y Sy hSy hymem
        refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
        refine ⟨univ 0, ?_, ?_⟩
        · simp [Expr.instantiate1, interpExpr, Level.eval]
        · exact univ_mem_univ 0
      · refine ⟨pi 1 A (fun _ => univ 0), ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
        · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
            hAmem (fun _ _ => univ_mem_univ 0)
    · refine ⟨?_, ?_⟩
      · first
          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
          | (rintro v ⟨rfl⟩
             intro z hz
             refine univ_mono ?_ z hz
             simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
      intro R SR hSR hRmem
      simp [interpExpr, Expr.instantiate1, updV, Level.eval,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSR
      subst hSR
      have hRmem' : R ∈ˢ relSpace V (ψ uN) A := hRmem
      refine ⟨?_, ?_⟩
      · -- the opened `∀ {β}, …`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨trivial, qlB (ψ uN) (ψ vN), ?_⟩
        refine ⟨?_, ?_⟩
        · first
            | (rintro v ⟨rfl⟩; exact fun z hz => hz)
            | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
            | (rintro v ⟨rfl⟩
               intro z hz
               refine univ_mono ?_ z hz
               simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
               by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
        intro B SB hSB hBmem
        have hSB' : SB = univ (ψ vN) := by
          simp only [interpExpr, Expr.instantiate1, reduceIte, Level.eval,
            Option.some.injEq] at hSB
          rw [← hSB]
          rfl
        rw [hSB'] at hBmem
        refine ⟨?_, ?_⟩
        · -- the opened `∀ (f : α → β), …`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨?_, qlV (ψ uN) (ψ vN), ?_⟩
          · -- the function space `α → β`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨trivial, ψ vN, ?_⟩
            refine ⟨?_, ?_⟩
            · first
                | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                | (rintro v ⟨rfl⟩
                   intro z hz
                   refine univ_mono ?_ z hz
                   simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                   by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
            intro a Sa hSa hamem
            refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
            refine ⟨B, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · exact hBmem
          · refine ⟨?_, ?_⟩
            · first
                | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                | (rintro v ⟨rfl⟩
                   intro z hz
                   refine univ_mono ?_ z hz
                   simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                   by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
            intro f Sf hSf hfmem
            simp [interpExpr, Expr.instantiate1, updV, Level.eval] at hSf
            subst hSf
            have hfmem' : f ∈ˢ pi (ψ vN) A (fun _ => B) := hfmem
            have hfapp : ∀ x, x ∈ˢ A → SetTheory.app f x ∈ˢ B :=
              fun x hx => app_mem hfmem' hx (fun _ _ => hBmem)
            refine ⟨?_, ?_⟩
            · -- the opened `∀ (h : invariance), Quot α r → β`
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨?_, qlQ (ψ uN) (ψ vN), ?_⟩
              · -- the invariance space `∀ a b, r a b → Eq β (f a) (f b)`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨trivial, 0, ?_⟩
                refine ⟨?_, ?_⟩
                · first
                    | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                    | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                    | (rintro v ⟨rfl⟩
                       intro z hz
                       refine univ_mono ?_ z hz
                       simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                       by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
                intro a Sa hSa hamem
                simp [interpExpr, Expr.instantiate1, updV] at hSa
                subst hSa
                refine ⟨?_, ?_⟩
                · -- opened `∀ b, r a b → Eq β (f a) (f b)`
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨trivial, 0, ?_⟩
                  refine ⟨?_, ?_⟩
                  · first
                      | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                      | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                      | (rintro v ⟨rfl⟩
                         intro z hz
                         refine univ_mono ?_ z hz
                         simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                         by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
                  intro b Sb hSb hbmem
                  simp [interpExpr, Expr.instantiate1, updV] at hSb
                  subst hSb
                  refine ⟨?_, ?_⟩
                  · -- opened `r a b → Eq β (f a) (f b)`
                    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                    refine ⟨?_, 0, ?_⟩
                    · -- AnnotOk of `r a b` (two app clauses)
                      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                      refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                          (by simp [Expr.instantiate1, AnnotOk]),
                          R, a, Nat.max (ψ uN) 1, A,
                          (fun _ => pi 1 A fun _ => univ 0),
                          ?_, ?_, hRmem', hamem, fun x hx => ?_⟩,
                        (by simp [Expr.instantiate1, AnnotOk]),
                        SetTheory.app R a, b, 1, A, (fun _ => univ 0),
                        ?_, ?_, ?_, hbmem, fun _ _ => univ_mem_univ 0⟩
                      · simp [interpExpr, Expr.instantiate1, updV]
                      · simp [interpExpr, Expr.instantiate1, updV]
                      · exact pi_mem_univ (u := ψ uN) (v := 1)
                          (B := fun _ => univ 0) hAmem
                          (fun _ _ => univ_mem_univ 0)
                      · simp [interpExpr, Expr.instantiate1, updV]
                      · simp [interpExpr, Expr.instantiate1, updV]
                      · exact app_mem hRmem' hamem (fun x hx =>
                          pi_mem_univ (u := ψ uN) (v := 1)
                            (B := fun _ => univ 0) hAmem
                            (fun _ _ => univ_mem_univ 0))
                    · refine ⟨?_, ?_⟩
                      · first
                          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                          | (rintro v ⟨rfl⟩
                             intro z hz
                             refine univ_mono ?_ z hz
                             simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
                      intro w Sw hSw hwmem
                      refine ⟨?_, ?_⟩
                      · -- AnnotOk of `Eq β (f a) (f b)`
                        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                        refine ⟨⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                            (by simp [Expr.instantiate1, AnnotOk]),
                            eqVal V (qlψ ψ), B,
                            Nat.max (ψ vN) (Nat.max (ψ vN) 1), univ (ψ vN),
                            (fun X => pi (Nat.max (ψ vN) 1) X fun _ =>
                              pi 1 X fun _ => univ 0),
                            ?_, ?_, eqVal_mem, hBmem,
                            fun X hX => eq_fibre_mem (ψ := qlψ ψ) hX⟩,
                          ⟨(by simp [Expr.instantiate1, AnnotOk]),
                            (by simp [Expr.instantiate1, AnnotOk]),
                            f, a, ψ vN, A, (fun _ => B),
                            ?_, ?_, hfmem', hamem, fun _ _ => hBmem⟩,
                          SetTheory.app (eqVal V (qlψ ψ)) B,
                          SetTheory.app f a, Nat.max (ψ vN) 1, B,
                          (fun _ => pi 1 B fun _ => univ 0),
                          ?_, ?_, eqVal_app_mem (ψ := qlψ ψ) hBmem,
                          hfapp a hamem,
                          fun y _ => pi_mem_univ (u := ψ vN) (v := 1)
                            (B := fun _ => univ 0) hBmem
                            (fun _ _ => univ_mem_univ 0)⟩,
                        ⟨(by simp [Expr.instantiate1, AnnotOk]),
                          (by simp [Expr.instantiate1, AnnotOk]),
                          f, b, ψ vN, A, (fun _ => B),
                          ?_, ?_, hfmem', hbmem, fun _ _ => hBmem⟩,
                        SetTheory.app (SetTheory.app (eqVal V (qlψ ψ)) B)
                          (SetTheory.app f a),
                        SetTheory.app f b, 1, B, (fun _ => univ 0),
                        ?_, ?_,
                        eqVal_app₂_mem (ψ := qlψ ψ) hBmem (hfapp a hamem),
                        hfapp b hbmem, fun _ _ => univ_mem_univ 0⟩
                        all_goals try simp [interpExpr, Expr.instantiate1,
                          updV, hfindE', hvalE', eqA,
                          ConstantInfo.toConstantVal]
                        all_goals try rfl
                      · -- fibre-universe of the proof binder (annotation 0)
                        refine ⟨SetTheory.app (SetTheory.app
                            (SetTheory.app (eqVal V (qlψ ψ)) B)
                            (SetTheory.app f a)) (SetTheory.app f b),
                          ?_, ?_⟩
                        · simp [interpExpr, Expr.instantiate1, updV, hfindE',
                            hvalE', eqA, ConstantInfo.toConstantVal]
                          try rfl
                        · rw [eqVal_app₃ (ψ := qlψ ψ) hBmem
                            (hfapp a hamem) (hfapp b hbmem)]
                          exact eqv_mem_univ _ _
                  · -- fibre-universe of the `b` binder (annotation
                    -- `imax 0 0`)
                    refine ⟨pi 0 (SetTheory.app (SetTheory.app R a) b)
                      (fun _ => SetTheory.app (SetTheory.app
                        (SetTheory.app (eqVal V (qlψ ψ)) B)
                        (SetTheory.app f a)) (SetTheory.app f b)), ?_, ?_⟩
                    · simp [interpExpr, Expr.instantiate1, updV, hfindE',
                        hvalE', eqA, ConstantInfo.toConstantVal, Level.eval]
                      try rfl
                    · exact hDom3 R hRmem' B hBmem f hfmem' a b hamem hbmem
                · -- fibre-universe of the `a` binder (annotation
                  -- `imax u (imax 0 0)`)
                  refine ⟨pi 0 A (fun b' =>
                    pi 0 (SetTheory.app (SetTheory.app R a) b') fun _ =>
                      SetTheory.app (SetTheory.app
                        (SetTheory.app (eqVal V (qlψ ψ)) B)
                        (SetTheory.app f a)) (SetTheory.app f b')), ?_, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV, hfindE',
                      hvalE', eqA, ConstantInfo.toConstantVal, Level.eval]
                    try rfl
                  · exact hDom2 R hRmem' B hBmem f hfmem' a hamem
              · refine ⟨?_, ?_⟩
                · first
                    | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                    | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                    | (rintro v ⟨rfl⟩
                       intro z hz
                       refine univ_mono ?_ z hz
                       simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                       by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
                intro h _Sh _hSh _hhmem
                refine ⟨?_, ?_⟩
                · -- the opened `Quot α r → β`
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨?_, ψ vN, ?_⟩
                  · -- AnnotOk of `Quot α r` (two app clauses)
                    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                    refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                        (by simp [Expr.instantiate1, AnnotOk]),
                        quotVal V ψ, A, ψ uN + 1, univ (ψ uN),
                        (fun X => pi (ψ uN + 1) (relSpace V (ψ uN) X)
                          fun _ => univ (ψ uN)),
                        ?_, ?_, quotVal_mem, hAmem,
                        fun X hX => quot_fibre_mem hX⟩,
                      (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (quotVal V ψ) A, R, ψ uN + 1,
                      relSpace V (ψ uN) A, (fun _ => univ (ψ uN)),
                      ?_, ?_, quotVal_app_mem hAmem, hRmem',
                      fun _ _ => univ_mem_univ (ψ uN)⟩
                    · simp [interpExpr, Expr.instantiate1, updV, hfindQ',
                        hvalQ', quotA, ConstantInfo.toConstantVal]
                      try rfl
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · simp [interpExpr, Expr.instantiate1, updV, hfindQ',
                        hvalQ', quotA, ConstantInfo.toConstantVal]
                      try rfl
                    · simp [interpExpr, Expr.instantiate1, updV]
                  · refine ⟨?_, ?_⟩
                    · first
                        | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                        | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                        | (rintro v ⟨rfl⟩
                           intro z hz
                           refine univ_mono ?_ z hz
                           simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                           by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
                    intro q _Sq _hSq _hqmem
                    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
                    refine ⟨B, ?_, ?_⟩
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · exact hBmem
                · -- fibre-universe of the `h` binder (annotation
                  -- `imax u v`)
                  refine ⟨pi (ψ vN)
                    (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
                    (fun _ => B), ?_, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV, hfindQ',
                      hvalQ', quotA, ConstantInfo.toConstantVal, Level.eval]
                    try rfl
                  · exact hQB R hRmem' B hBmem
            · -- fibre-universe of the `f` binder
              refine ⟨pi (qlQ (ψ uN) (ψ vN))
                (pi 0 A fun a' => pi 0 A fun b' =>
                  pi 0 (SetTheory.app (SetTheory.app R a') b') fun _ =>
                    SetTheory.app (SetTheory.app
                      (SetTheory.app (eqVal V (qlψ ψ)) B)
                      (SetTheory.app f a')) (SetTheory.app f b')) (fun _ =>
                pi (ψ vN)
                  (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
                  fun _ => B), ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                  hfindQ', hvalQ', eqA, quotA, ConstantInfo.toConstantVal,
                  Level.eval, uN, vN, qlQ, qlψ,
                  -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                try rfl
              · exact hT4 R hRmem' B hBmem f hfmem'
        · -- fibre-universe of the `β` binder
          refine ⟨pi (qlV (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B)
            (fun f' =>
              pi (qlQ (ψ uN) (ψ vN))
                (pi 0 A fun a' => pi 0 A fun b' =>
                  pi 0 (SetTheory.app (SetTheory.app R a') b') fun _ =>
                    SetTheory.app (SetTheory.app
                      (SetTheory.app (eqVal V (qlψ ψ)) B)
                      (SetTheory.app f' a')) (SetTheory.app f' b'))
                fun _ =>
                pi (ψ vN)
                  (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
                  fun _ => B), ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
              hfindQ', hvalQ', eqA, quotA, ConstantInfo.toConstantVal,
              Level.eval, uN, vN, qlQ, qlV, qlψ,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl
          · exact hT3 R hRmem' B hBmem
      · -- fibre-universe of the `r` binder
        refine ⟨pi (qlB (ψ uN) (ψ vN)) (univ (ψ vN)) (fun B' =>
          pi (qlV (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B') fun f' =>
            pi (qlQ (ψ uN) (ψ vN))
              (pi 0 A fun a' => pi 0 A fun b' =>
                pi 0 (SetTheory.app (SetTheory.app R a') b') fun _ =>
                  SetTheory.app (SetTheory.app
                    (SetTheory.app (eqVal V (qlψ ψ)) B')
                    (SetTheory.app f' a')) (SetTheory.app f' b')) fun _ =>
              pi (ψ vN)
                (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
                fun _ => B'), ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
            hfindQ', hvalQ', eqA, quotA, ConstantInfo.toConstantVal,
            Level.eval, uN, vN, qlQ, qlV, qlB, qlψ,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · exact hT2 R hRmem'
  · -- fibre-universe of the `α` binder
    refine ⟨pi (qlR (ψ uN) (ψ vN)) (relSpace V (ψ uN) A) (fun R' =>
      pi (qlB (ψ uN) (ψ vN)) (univ (ψ vN)) fun B' =>
        pi (qlV (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B') fun f' =>
          pi (qlQ (ψ uN) (ψ vN))
            (pi 0 A fun a' => pi 0 A fun b' =>
              pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
                SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V (qlψ ψ)) B')
                  (SetTheory.app f' a')) (SetTheory.app f' b')) fun _ =>
            pi (ψ vN)
              (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
              fun _ => B'), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
        hfindQ', hvalQ', eqA, quotA, ConstantInfo.toConstantVal,
        Level.eval, uN, vN, relSpace, qlQ, qlV, qlB, qlR, qlψ,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · exact hT1

/-! ## `Quot.ind` -/

/-- Interpretation of `Quot.ind`'s pinned type, computed (the whole
telescope is propositional: every binder annotation evaluates to 0). -/
theorem interp_quotInd_type {cval : ConstVal V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ') :
    interpClosed V cval env ψ quotIndA.toConstantVal.type =
      some (pi 0 (univ (ψ uN)) fun A =>
        pi 0 (relSpace V (ψ uN) A) fun R =>
          pi 0 (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
              fun _ => univ 0) fun B =>
            pi 0 (pi 0 A fun a => SetTheory.app B
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (quotMkVal V ψ) A) R) a)) fun _ =>
              pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
                fun q => SetTheory.app B q) := by
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA := hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  have hfindMk' : env.find? ((Name.anonymous.str "Quot").str "mk") =
      some quotMkA := hfindMk
  have hvalMk' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "mk") ψ' = quotMkVal V ψ' :=
    hvalMk
  simp only [interpClosed, quotIndA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindQ', hvalQ', hfindMk', hvalMk', quotA, quotMkA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, Expr.instantiate1, updV, uN, relSpace,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `Quot.ind`'s value inhabits its type (the class surjectivity
argument: every element of the quotient is a class, and the motive's
truth at classes is given by the minor premise). -/
theorem quotInd_key {cval : ConstVal V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ') :
    ∃ T, interpClosed V cval env ψ quotIndA.toConstantVal.type = some T ∧
      quotIndVal V ψ ∈ˢ T := by
  refine ⟨_, interp_quotInd_type hfindQ hvalQ hfindMk hvalMk, ?_⟩
  simp only [quotIndVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun R hR => ?_
  rw [quotVal_app₂ hA hR]
  refine lam_mem (V := V) fun B hB => ?_
  have hMk : (pi 0 A fun a => SetTheory.app B
      (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R)
        a)) =
      pi 0 A fun a => SetTheory.app B (quotClass (ψ uN) A R a) :=
    pi_congr fun a ha => by rw [quotMkVal_app₃ hA hR ha]
  rw [hMk]
  refine lam_mem (V := V) fun mk hmk => ?_
  refine lam_mem (V := V) fun q hq => ?_
  have hBfib : ∀ x, x ∈ˢ quotSet (ψ uN) A R →
      SetTheory.app B x ∈ˢ univ 0 :=
    fun x hx => app_mem hB hx (fun _ _ => univ_mem_univ 0)
  obtain ⟨a, ha, rfl⟩ := quotClass_surj hq
  have hmka : SetTheory.app mk a ∈ˢ
      SetTheory.app B (quotClass (ψ uN) A R a) :=
    app_mem hmk ha (fun x hx => hBfib _ (quotClass_mem hx))
  have hpt := mem_univ_zero (hBfib _ (quotClass_mem ha)) hmka
  exact hpt ▸ hmka

/-- `Quot.ind`'s type carries truthful annotations. -/
theorem annotOk_quotInd_type {cval : ConstVal V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) quotIndA.toConstantVal.type := by
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA := hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  have hfindMk' : env.find? ((Name.anonymous.str "Quot").str "mk") =
      some quotMkA := hfindMk
  have hvalMk' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "mk") ψ' = quotMkVal V ψ' :=
    hvalMk
  simp only [quotIndA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, 0, ?_⟩
  refine ⟨?_, ?_⟩
  · first
      | (rintro v ⟨rfl⟩; exact fun z hz => hz)
      | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
      | (rintro v ⟨rfl⟩
         intro z hz
         refine univ_mono ?_ z hz
         simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
         by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  -- the telescope-suffix universe facts, parametric in the point
  have hBS : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
        fun _ => univ 0) ∈ˢ univ (Nat.max (ψ uN) 1) := by
    intro R' hR'
    rw [quotVal_app₂ hAmem hR']
    exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
      (quotSet_mem_univ hAmem) (fun _ _ => univ_mem_univ 0)
  have hMkS : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      ∀ B', B' ∈ˢ pi 1 (quotSet (ψ uN) A R') (fun _ => univ 0) →
      (pi 0 A fun a => SetTheory.app B'
        (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R')
          a)) ∈ˢ univ 0 := by
    intro R' hR' B' hB'
    refine pi_mem_univ (u := ψ uN) (v := 0) hAmem (fun a ha => ?_)
    rw [quotMkVal_app₃ hAmem hR' ha]
    exact app_mem hB' (quotClass_mem ha) (fun _ _ => univ_mem_univ 0)
  have hQS : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      ∀ B', B' ∈ˢ pi 1 (quotSet (ψ uN) A R') (fun _ => univ 0) →
      (pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
        fun q => SetTheory.app B' q) ∈ˢ univ 0 := by
    intro R' hR' B' hB'
    rw [quotVal_app₂ hAmem hR']
    exact pi_mem_univ (u := ψ uN) (v := 0) (quotSet_mem_univ hAmem)
      (fun q hq => app_mem hB' hq (fun _ _ => univ_mem_univ 0))
  have hT3 : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      ∀ B', B' ∈ˢ pi 1 (quotSet (ψ uN) A R') (fun _ => univ 0) →
      (pi 0 (pi 0 A fun a => SetTheory.app B'
        (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R')
          a)) fun _ =>
        pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
          fun q => SetTheory.app B' q) ∈ˢ univ 0 := by
    intro R' hR' B' hB'
    exact pi_mem_univ (u := 0) (v := 0) (hMkS R' hR' B' hB')
      (fun _ _ => hQS R' hR' B' hB')
  have hT2 : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      (pi 0 (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
        fun _ => univ 0) fun B' =>
        pi 0 (pi 0 A fun a => SetTheory.app B'
          (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A)
            R') a)) fun _ =>
          pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
            fun q => SetTheory.app B' q) ∈ˢ univ 0 := by
    intro R' hR'
    refine pi_mem_univ (u := Nat.max (ψ uN) 1) (v := 0) (hBS R' hR')
      (fun B' hB' => ?_)
    refine hT3 R' hR' B' ?_
    rwa [quotVal_app₂ hAmem hR'] at hB'
  have hT1 : (pi 0 (relSpace V (ψ uN) A) fun R' =>
      pi 0 (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
        fun _ => univ 0) fun B' =>
        pi 0 (pi 0 A fun a => SetTheory.app B'
          (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A)
            R') a)) fun _ =>
          pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
            fun q => SetTheory.app B' q) ∈ˢ univ 0 :=
    pi_mem_univ (u := Nat.max (ψ uN) 1) (v := 0) (relSpace_mem_univ hAmem)
      (fun R' hR' => hT2 R' hR')
  refine ⟨?_, ?_⟩
  · -- the opened `∀ {r}, …`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, 0, ?_⟩
    · -- the relation space `α → α → Prop`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, Nat.max (ψ uN) 1, ?_⟩
      refine ⟨?_, ?_⟩
      · first
          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
          | (rintro v ⟨rfl⟩
             intro z hz
             refine univ_mono ?_ z hz
             simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
      intro x Sx hSx hxmem
      have hSx' : Sx = A := by
        simp only [interpExpr, updV, Expr.instantiate1, reduceIte,
          Option.some.injEq] at hSx
        exact hSx.symm
      rw [hSx'] at hxmem
      refine ⟨?_, ?_⟩
      · try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨trivial, 1, ?_⟩
        refine ⟨?_, ?_⟩
        · first
            | (rintro v ⟨rfl⟩; exact fun z hz => hz)
            | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
            | (rintro v ⟨rfl⟩
               intro z hz
               refine univ_mono ?_ z hz
               simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
               by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
        intro y Sy hSy hymem
        refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
        refine ⟨univ 0, ?_, ?_⟩
        · simp [Expr.instantiate1, interpExpr, Level.eval]
        · exact univ_mem_univ 0
      · refine ⟨pi 1 A (fun _ => univ 0), ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
        · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
            hAmem (fun _ _ => univ_mem_univ 0)
    · refine ⟨?_, ?_⟩
      · first
          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
          | (rintro v ⟨rfl⟩
             intro z hz
             refine univ_mono ?_ z hz
             simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
      intro R SR hSR hRmem
      simp [interpExpr, Expr.instantiate1, updV, Level.eval,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSR
      subst hSR
      have hRmem' : R ∈ˢ relSpace V (ψ uN) A := hRmem
      refine ⟨?_, ?_⟩
      · -- the opened `∀ {β}, …`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨?_, 0, ?_⟩
        · -- the motive space `Quot α r → Prop`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨?_, 1, ?_⟩
          · -- AnnotOk of `Quot α r`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                (by simp [Expr.instantiate1, AnnotOk]),
                quotVal V ψ, A, ψ uN + 1, univ (ψ uN),
                (fun X => pi (ψ uN + 1) (relSpace V (ψ uN) X)
                  fun _ => univ (ψ uN)),
                ?_, ?_, quotVal_mem, hAmem,
                fun X hX => quot_fibre_mem hX⟩,
              (by simp [Expr.instantiate1, AnnotOk]),
              SetTheory.app (quotVal V ψ) A, R, ψ uN + 1,
              relSpace V (ψ uN) A, (fun _ => univ (ψ uN)),
              ?_, ?_, quotVal_app_mem hAmem, hRmem',
              fun _ _ => univ_mem_univ (ψ uN)⟩
            all_goals try simp [interpExpr, Expr.instantiate1, updV,
              hfindQ', hvalQ', quotA, ConstantInfo.toConstantVal]
            all_goals try rfl
          · refine ⟨?_, ?_⟩
            · first
                | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                | (rintro v ⟨rfl⟩
                   intro z hz
                   refine univ_mono ?_ z hz
                   simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                   by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
            intro x Sx hSx hxmem
            refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
            refine ⟨univ 0, ?_, ?_⟩
            · simp [Expr.instantiate1, interpExpr, Level.eval]
            · exact univ_mem_univ 0
        · refine ⟨?_, ?_⟩
          · first
              | (rintro v ⟨rfl⟩; exact fun z hz => hz)
              | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
              | (rintro v ⟨rfl⟩
                 intro z hz
                 refine univ_mono ?_ z hz
                 simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                 by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
          intro B SB hSB hBmem
          simp [interpExpr, Expr.instantiate1, updV, Level.eval, hfindQ',
            hvalQ', quotA, ConstantInfo.toConstantVal,
            -ite_eq_left_iff, -ite_eq_right_iff,
            -Nat.max_eq_zero_iff] at hSB
          subst hSB
          have hBmem' : B ∈ˢ pi 1 (quotSet (ψ uN) A R)
              (fun _ => univ 0) := by
            have hBmem₀ : B ∈ˢ pi 1
                (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
                (fun _ => univ 0) := hBmem
            rwa [quotVal_app₂ hAmem hRmem'] at hBmem₀
          refine ⟨?_, ?_⟩
          · -- the opened `∀ (mk), …`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨?_, 0, ?_⟩
            · -- the minor-premise space `(a : α) → β (Quot.mk α r a)`
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨trivial, 0, ?_⟩
              refine ⟨?_, ?_⟩
              · first
                  | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                  | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                  | (rintro v ⟨rfl⟩
                     intro z hz
                     refine univ_mono ?_ z hz
                     simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                     by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
              intro a Sa hSa hamem
              simp [interpExpr, Expr.instantiate1, updV] at hSa
              subst hSa
              refine ⟨?_, ?_⟩
              · -- the body `β (Quot.mk α r a)` (nested app clauses)
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                  ⟨⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                      (by simp [Expr.instantiate1, AnnotOk]),
                      quotMkVal V ψ, A, ψ uN, univ (ψ uN),
                      (fun X => pi (ψ uN) (relSpace V (ψ uN) X) fun R' =>
                        pi (ψ uN) X fun _ => quotSet (ψ uN) X R'),
                      ?_, ?_, quotMkVal_mem, hAmem,
                      fun X hX => mk_fibre_mem hX⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                    SetTheory.app (quotMkVal V ψ) A, R, ψ uN,
                    relSpace V (ψ uN) A,
                    (fun R' => pi (ψ uN) A fun _ => quotSet (ψ uN) A R'),
                    ?_, ?_, quotMkVal_app_mem hAmem, hRmem',
                    fun R' _ => mkA_fibre_mem hAmem⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                  SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R, a,
                  ψ uN, A, (fun _ => quotSet (ψ uN) A R),
                  ?_, ?_, quotMkVal_app₂_mem hAmem hRmem', hamem,
                  fun _ _ => quotSet_mem_univ hAmem⟩,
                  B,
                  SetTheory.app (SetTheory.app
                    (SetTheory.app (quotMkVal V ψ) A) R) a,
                  1, SetTheory.app (SetTheory.app (quotVal V ψ) A) R,
                  (fun _ => univ 0),
                  ?_, ?_, hBmem, ?_, fun _ _ => univ_mem_univ 0⟩
                all_goals try simp [interpExpr, Expr.instantiate1, updV,
                  hfindQ', hvalQ', hfindMk', hvalMk', quotA, quotMkA,
                  ConstantInfo.toConstantVal]
                all_goals try rfl
                rw [quotVal_app₂ hAmem hRmem']
                exact quotMkVal_app₃_mem hAmem hRmem' hamem
              · -- fibre-universe of the `a` binder (annotation 0)
                refine ⟨SetTheory.app B (SetTheory.app (SetTheory.app
                    (SetTheory.app (quotMkVal V ψ) A) R) a), ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV, hfindMk',
                    hvalMk', quotMkA, ConstantInfo.toConstantVal]
                  try rfl
                · rw [quotMkVal_app₃ hAmem hRmem' hamem]
                  exact app_mem hBmem' (quotClass_mem hamem)
                    (fun _ _ => univ_mem_univ 0)
            · refine ⟨?_, ?_⟩
              · first
                  | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                  | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                  | (rintro v ⟨rfl⟩
                     intro z hz
                     refine univ_mono ?_ z hz
                     simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                     by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
              intro mk _Smk _hSmk _hmkmem
              refine ⟨?_, ?_⟩
              · -- the opened `∀ (q : Quot α r), β q`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨?_, 0, ?_⟩
                · -- AnnotOk of `Quot α r`
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                      (by simp [Expr.instantiate1, AnnotOk]),
                      quotVal V ψ, A, ψ uN + 1, univ (ψ uN),
                      (fun X => pi (ψ uN + 1) (relSpace V (ψ uN) X)
                        fun _ => univ (ψ uN)),
                      ?_, ?_, quotVal_mem, hAmem,
                      fun X hX => quot_fibre_mem hX⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                    SetTheory.app (quotVal V ψ) A, R, ψ uN + 1,
                    relSpace V (ψ uN) A, (fun _ => univ (ψ uN)),
                    ?_, ?_, quotVal_app_mem hAmem, hRmem',
                    fun _ _ => univ_mem_univ (ψ uN)⟩
                  all_goals try simp [interpExpr, Expr.instantiate1, updV,
                    hfindQ', hvalQ', quotA, ConstantInfo.toConstantVal]
                  all_goals try rfl
                · refine ⟨?_, ?_⟩
                  · first
                      | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                      | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                      | (rintro v ⟨rfl⟩
                         intro z hz
                         refine univ_mono ?_ z hz
                         simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                         by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
                  intro q Sq hSq hqmem
                  simp [interpExpr, Expr.instantiate1, updV, hfindQ',
                    hvalQ', quotA, ConstantInfo.toConstantVal] at hSq
                  subst hSq
                  refine ⟨?_, ?_⟩
                  · -- the body `β q` (one app clause)
                    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                    refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                      (by simp [Expr.instantiate1, AnnotOk]),
                      B, q, 1,
                      SetTheory.app (SetTheory.app (quotVal V ψ) A) R,
                      (fun _ => univ 0),
                      ?_, ?_, hBmem, hqmem, fun _ _ => univ_mem_univ 0⟩
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · simp [interpExpr, Expr.instantiate1, updV]
                  · -- fibre-universe of the `q` binder (annotation 0)
                    refine ⟨SetTheory.app B q, ?_, ?_⟩
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · exact app_mem hBmem hqmem
                        (fun _ _ => univ_mem_univ 0)
              · -- fibre-universe of the `mk` binder
                refine ⟨pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A)
                    R) (fun q => SetTheory.app B q), ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV, hfindQ',
                    hvalQ', quotA, ConstantInfo.toConstantVal, Level.eval]
                  try rfl
                · exact hQS R hRmem' B hBmem'
          · -- fibre-universe of the `β` binder
            refine ⟨pi 0 (pi 0 A fun a => SetTheory.app B
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (quotMkVal V ψ) A) R) a)) (fun _ =>
              pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
                fun q => SetTheory.app B q), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
                hfindMk', hvalMk', quotA, quotMkA,
                ConstantInfo.toConstantVal, Level.eval]
              try rfl
            · exact hT3 R hRmem' B hBmem'
      · -- fibre-universe of the `r` binder
        refine ⟨pi 0 (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A)
            R) fun _ => univ 0) (fun B' =>
          pi 0 (pi 0 A fun a => SetTheory.app B'
            (SetTheory.app (SetTheory.app
              (SetTheory.app (quotMkVal V ψ) A) R) a)) fun _ =>
            pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
              fun q => SetTheory.app B' q), ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
            hfindMk', hvalMk', quotA, quotMkA, ConstantInfo.toConstantVal,
            Level.eval]
          try rfl
        · exact hT2 R hRmem'
  · -- fibre-universe of the `α` binder
    refine ⟨pi 0 (relSpace V (ψ uN) A) (fun R' =>
      pi 0 (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
        fun _ => univ 0) fun B' =>
        pi 0 (pi 0 A fun a => SetTheory.app B'
          (SetTheory.app (SetTheory.app
            (SetTheory.app (quotMkVal V ψ) A) R') a)) fun _ =>
          pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R')
            fun q => SetTheory.app B' q), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
        hfindMk', hvalMk', quotA, quotMkA, ConstantInfo.toConstantVal,
        Level.eval, uN, relSpace,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · exact hT1

/-! ## `Quot.sound` -/

/-- Interpretation of `Quot.sound`'s pinned type, computed (the whole
telescope is propositional). -/
theorem interp_quotSound_type {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ') :
    interpClosed V cval env ψ quotSoundA.toConstantVal.type =
      some (pi 0 (univ (ψ uN)) fun A =>
        pi 0 (relSpace V (ψ uN) A) fun R =>
          pi 0 A fun a => pi 0 A fun b =>
            pi 0 (SetTheory.app (SetTheory.app R a) b) fun _ =>
              SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ)
                (SetTheory.app (SetTheory.app (quotVal V ψ) A) R))
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (quotMkVal V ψ) A) R) a))
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (quotMkVal V ψ) A) R) b)) := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA := hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  have hfindMk' : env.find? ((Name.anonymous.str "Quot").str "mk") =
      some quotMkA := hfindMk
  have hvalMk' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "mk") ψ' = quotMkVal V ψ' :=
    hvalMk
  simp only [interpClosed, quotSoundA, ConstantInfo.toConstantVal,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindE', hvalE', hfindQ', hvalQ', hfindMk', hvalMk', eqA, quotA,
    quotMkA, List.length_cons, List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, Expr.instantiate1, updV, uN, relSpace,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `Quot.sound`'s value inhabits its type: related elements share
their class (`quotSound`), so the interpreted equality is true. -/
theorem quotSound_key {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ') :
    ∃ T, interpClosed V cval env ψ quotSoundA.toConstantVal.type = some T ∧
      quotSoundVal V ψ ∈ˢ T := by
  refine ⟨_, interp_quotSound_type hfindE hvalE hfindQ hvalQ hfindMk
    hvalMk, ?_⟩
  simp only [quotSoundVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun R hR => ?_
  refine lam_mem (V := V) fun a ha => ?_
  refine lam_mem (V := V) fun b hb => ?_
  refine lam_mem (V := V) fun w hw => ?_
  rw [quotVal_app₂ hA hR, quotMkVal_app₃ hA hR ha, quotMkVal_app₃ hA hR hb,
    eqVal_app₃ (quotSet_mem_univ hA) (quotClass_mem ha) (quotClass_mem hb),
    quotSound ha hb hw]
  exact pt_mem_eqv_self _

/-- `Quot.sound`'s type carries truthful annotations. -/
theorem annotOk_quotSound_type {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) quotSoundA.toConstantVal.type := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA := hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  have hfindMk' : env.find? ((Name.anonymous.str "Quot").str "mk") =
      some quotMkA := hfindMk
  have hvalMk' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "mk") ψ' = quotMkVal V ψ' :=
    hvalMk
  simp only [quotSoundA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, 0, ?_⟩
  refine ⟨?_, ?_⟩
  · first
      | (rintro v ⟨rfl⟩; exact fun z hz => hz)
      | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
      | (rintro v ⟨rfl⟩
         intro z hz
         refine univ_mono ?_ z hz
         simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
         by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  -- the interpreted equality statement collapses to a truth value
  have hEq3 : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      ∀ a' b', a' ∈ˢ A → b' ∈ˢ A →
      SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ)
        (SetTheory.app (SetTheory.app (quotVal V ψ) A) R'))
        (SetTheory.app (SetTheory.app
          (SetTheory.app (quotMkVal V ψ) A) R') a'))
        (SetTheory.app (SetTheory.app
          (SetTheory.app (quotMkVal V ψ) A) R') b') =
      eqv (quotClass (ψ uN) A R' a') (quotClass (ψ uN) A R' b') := by
    intro R' hR' a' b' ha' hb'
    rw [quotVal_app₂ hAmem hR', quotMkVal_app₃ hAmem hR' ha',
      quotMkVal_app₃ hAmem hR' hb',
      eqVal_app₃ (quotSet_mem_univ hAmem) (quotClass_mem ha')
        (quotClass_mem hb')]
  have hW : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      ∀ a' b', a' ∈ˢ A → b' ∈ˢ A →
      (pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
        SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ)
          (SetTheory.app (SetTheory.app (quotVal V ψ) A) R'))
          (SetTheory.app (SetTheory.app
            (SetTheory.app (quotMkVal V ψ) A) R') a'))
          (SetTheory.app (SetTheory.app
            (SetTheory.app (quotMkVal V ψ) A) R') b')) ∈ˢ univ 0 := by
    intro R' hR' a' b' ha' hb'
    simp only [hEq3 R' hR' a' b' ha' hb']
    exact pi_mem_univ (u := 0) (v := 0)
      (relSpace_app₂_mem hAmem hR' ha' hb') (fun _ _ => eqv_mem_univ _ _)
  have hB4 : ∀ R', R' ∈ˢ relSpace V (ψ uN) A → ∀ a', a' ∈ˢ A →
      (pi 0 A fun b' =>
        pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
          SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ)
            (SetTheory.app (SetTheory.app (quotVal V ψ) A) R'))
            (SetTheory.app (SetTheory.app
              (SetTheory.app (quotMkVal V ψ) A) R') a'))
            (SetTheory.app (SetTheory.app
              (SetTheory.app (quotMkVal V ψ) A) R') b')) ∈ˢ univ 0 := by
    intro R' hR' a' ha'
    exact pi_mem_univ (u := ψ uN) (v := 0) hAmem
      (fun b' hb' => hW R' hR' a' b' ha' hb')
  have hA3 : ∀ R', R' ∈ˢ relSpace V (ψ uN) A →
      (pi 0 A fun a' => pi 0 A fun b' =>
        pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
          SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ)
            (SetTheory.app (SetTheory.app (quotVal V ψ) A) R'))
            (SetTheory.app (SetTheory.app
              (SetTheory.app (quotMkVal V ψ) A) R') a'))
            (SetTheory.app (SetTheory.app
              (SetTheory.app (quotMkVal V ψ) A) R') b')) ∈ˢ univ 0 := by
    intro R' hR'
    exact pi_mem_univ (u := ψ uN) (v := 0) hAmem
      (fun a' ha' => hB4 R' hR' a' ha')
  have hT1 : (pi 0 (relSpace V (ψ uN) A) fun R' =>
      pi 0 A fun a' => pi 0 A fun b' =>
        pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
          SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ)
            (SetTheory.app (SetTheory.app (quotVal V ψ) A) R'))
            (SetTheory.app (SetTheory.app
              (SetTheory.app (quotMkVal V ψ) A) R') a'))
            (SetTheory.app (SetTheory.app
              (SetTheory.app (quotMkVal V ψ) A) R') b')) ∈ˢ univ 0 :=
    pi_mem_univ (u := Nat.max (ψ uN) 1) (v := 0) (relSpace_mem_univ hAmem)
      (fun R' hR' => hA3 R' hR')
  refine ⟨?_, ?_⟩
  · -- the opened `∀ {r}, …`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, 0, ?_⟩
    · -- the relation space `α → α → Prop`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, Nat.max (ψ uN) 1, ?_⟩
      refine ⟨?_, ?_⟩
      · first
          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
          | (rintro v ⟨rfl⟩
             intro z hz
             refine univ_mono ?_ z hz
             simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
      intro x Sx hSx hxmem
      have hSx' : Sx = A := by
        simp only [interpExpr, updV, Expr.instantiate1, reduceIte,
          Option.some.injEq] at hSx
        exact hSx.symm
      rw [hSx'] at hxmem
      refine ⟨?_, ?_⟩
      · try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨trivial, 1, ?_⟩
        refine ⟨?_, ?_⟩
        · first
            | (rintro v ⟨rfl⟩; exact fun z hz => hz)
            | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
            | (rintro v ⟨rfl⟩
               intro z hz
               refine univ_mono ?_ z hz
               simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
               by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
        intro y Sy hSy hymem
        refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
        refine ⟨univ 0, ?_, ?_⟩
        · simp [Expr.instantiate1, interpExpr, Level.eval]
        · exact univ_mem_univ 0
      · refine ⟨pi 1 A (fun _ => univ 0), ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
        · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
            hAmem (fun _ _ => univ_mem_univ 0)
    · refine ⟨?_, ?_⟩
      · first
          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
          | (rintro v ⟨rfl⟩
             intro z hz
             refine univ_mono ?_ z hz
             simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
      intro R SR hSR hRmem
      simp [interpExpr, Expr.instantiate1, updV, Level.eval,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSR
      subst hSR
      have hRmem' : R ∈ˢ relSpace V (ψ uN) A := hRmem
      refine ⟨?_, ?_⟩
      · -- the opened `∀ {a : α}, …`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨trivial, 0, ?_⟩
        refine ⟨?_, ?_⟩
        · first
            | (rintro v ⟨rfl⟩; exact fun z hz => hz)
            | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
            | (rintro v ⟨rfl⟩
               intro z hz
               refine univ_mono ?_ z hz
               simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
               by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
        intro a Sa hSa hamem
        simp [interpExpr, Expr.instantiate1, updV] at hSa
        subst hSa
        refine ⟨?_, ?_⟩
        · -- the opened `∀ {b : α}, …`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨trivial, 0, ?_⟩
          refine ⟨?_, ?_⟩
          · first
              | (rintro v ⟨rfl⟩; exact fun z hz => hz)
              | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
              | (rintro v ⟨rfl⟩
                 intro z hz
                 refine univ_mono ?_ z hz
                 simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                 by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
          intro b Sb hSb hbmem
          simp [interpExpr, Expr.instantiate1, updV] at hSb
          subst hSb
          have hQD : SetTheory.app (SetTheory.app (quotVal V ψ) A) R ∈ˢ
              univ (ψ uN) := quotVal_app₂_mem hAmem hRmem'
          have hsA : SetTheory.app (SetTheory.app
              (SetTheory.app (quotMkVal V ψ) A) R) a ∈ˢ
              SetTheory.app (SetTheory.app (quotVal V ψ) A) R := by
            rw [quotVal_app₂ hAmem hRmem']
            exact quotMkVal_app₃_mem hAmem hRmem' hamem
          have hsB : SetTheory.app (SetTheory.app
              (SetTheory.app (quotMkVal V ψ) A) R) b ∈ˢ
              SetTheory.app (SetTheory.app (quotVal V ψ) A) R := by
            rw [quotVal_app₂ hAmem hRmem']
            exact quotMkVal_app₃_mem hAmem hRmem' hbmem
          refine ⟨?_, ?_⟩
          · -- the opened `r a b → Eq (Quot α r) (mk a) (mk b)`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨?_, 0, ?_⟩
            · -- AnnotOk of `r a b` (two app clauses)
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                  (by simp [Expr.instantiate1, AnnotOk]),
                  R, a, Nat.max (ψ uN) 1, A,
                  (fun _ => pi 1 A fun _ => univ 0),
                  ?_, ?_, hRmem', hamem,
                  fun x hx => pi_mem_univ (u := ψ uN) (v := 1)
                    (B := fun _ => univ 0) hAmem
                    (fun _ _ => univ_mem_univ 0)⟩,
                (by simp [Expr.instantiate1, AnnotOk]),
                SetTheory.app R a, b, 1, A, (fun _ => univ 0),
                ?_, ?_, ?_, hbmem, fun _ _ => univ_mem_univ 0⟩
              all_goals try simp [interpExpr, Expr.instantiate1, updV]
              exact app_mem hRmem' hamem (fun x hx =>
                pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
                  hAmem (fun _ _ => univ_mem_univ 0))
            · refine ⟨?_, ?_⟩
              · first
                  | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                  | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                  | (rintro v ⟨rfl⟩
                     intro z hz
                     refine univ_mono ?_ z hz
                     simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
                     by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
              intro w Sw hSw hwmem
              refine ⟨?_, ?_⟩
              · -- AnnotOk of `Eq (Quot α r) (mk a) (mk b)`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                    -- `Quot α r` (two app clauses)
                    ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                      (by simp [Expr.instantiate1, AnnotOk]),
                      quotVal V ψ, A, ψ uN + 1, univ (ψ uN),
                      (fun X => pi (ψ uN + 1) (relSpace V (ψ uN) X)
                        fun _ => univ (ψ uN)),
                      ?_, ?_, quotVal_mem, hAmem,
                      fun X hX => quot_fibre_mem hX⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                    SetTheory.app (quotVal V ψ) A, R, ψ uN + 1,
                    relSpace V (ψ uN) A, (fun _ => univ (ψ uN)),
                    ?_, ?_, quotVal_app_mem hAmem, hRmem',
                    fun _ _ => univ_mem_univ (ψ uN)⟩,
                    eqVal V ψ,
                    SetTheory.app (SetTheory.app (quotVal V ψ) A) R,
                    Nat.max (ψ uN) (Nat.max (ψ uN) 1), univ (ψ uN),
                    (fun X => pi (Nat.max (ψ uN) 1) X fun _ =>
                      pi 1 X fun _ => univ 0),
                    ?_, ?_, eqVal_mem, hQD,
                    fun X hX => eq_fibre_mem hX⟩,
                  -- `Quot.mk α r a` (three app clauses)
                  ⟨⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                      (by simp [Expr.instantiate1, AnnotOk]),
                      quotMkVal V ψ, A, ψ uN, univ (ψ uN),
                      (fun X => pi (ψ uN) (relSpace V (ψ uN) X) fun R' =>
                        pi (ψ uN) X fun _ => quotSet (ψ uN) X R'),
                      ?_, ?_, quotMkVal_mem, hAmem,
                      fun X hX => mk_fibre_mem hX⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                    SetTheory.app (quotMkVal V ψ) A, R, ψ uN,
                    relSpace V (ψ uN) A,
                    (fun R' => pi (ψ uN) A fun _ => quotSet (ψ uN) A R'),
                    ?_, ?_, quotMkVal_app_mem hAmem, hRmem',
                    fun R' _ => mkA_fibre_mem hAmem⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                  SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R, a,
                  ψ uN, A, (fun _ => quotSet (ψ uN) A R),
                  ?_, ?_, quotMkVal_app₂_mem hAmem hRmem', hamem,
                  fun _ _ => quotSet_mem_univ hAmem⟩,
                  SetTheory.app (eqVal V ψ)
                    (SetTheory.app (SetTheory.app (quotVal V ψ) A) R),
                  SetTheory.app (SetTheory.app
                    (SetTheory.app (quotMkVal V ψ) A) R) a,
                  Nat.max (ψ uN) 1,
                  SetTheory.app (SetTheory.app (quotVal V ψ) A) R,
                  (fun _ => pi 1 (SetTheory.app (SetTheory.app
                    (quotVal V ψ) A) R) fun _ => univ 0),
                  ?_, ?_, eqVal_app_mem hQD, hsA,
                  fun y _ => pi_mem_univ (u := ψ uN) (v := 1)
                    (B := fun _ => univ 0) hQD
                    (fun _ _ => univ_mem_univ 0)⟩,
                -- `Quot.mk α r b` (three app clauses)
                ⟨⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                    (by simp [Expr.instantiate1, AnnotOk]),
                    quotMkVal V ψ, A, ψ uN, univ (ψ uN),
                    (fun X => pi (ψ uN) (relSpace V (ψ uN) X) fun R' =>
                      pi (ψ uN) X fun _ => quotSet (ψ uN) X R'),
                    ?_, ?_, quotMkVal_mem, hAmem,
                    fun X hX => mk_fibre_mem hX⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                  SetTheory.app (quotMkVal V ψ) A, R, ψ uN,
                  relSpace V (ψ uN) A,
                  (fun R' => pi (ψ uN) A fun _ => quotSet (ψ uN) A R'),
                  ?_, ?_, quotMkVal_app_mem hAmem, hRmem',
                  fun R' _ => mkA_fibre_mem hAmem⟩,
                (by simp [Expr.instantiate1, AnnotOk]),
                SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R, b,
                ψ uN, A, (fun _ => quotSet (ψ uN) A R),
                ?_, ?_, quotMkVal_app₂_mem hAmem hRmem', hbmem,
                fun _ _ => quotSet_mem_univ hAmem⟩,
                SetTheory.app (SetTheory.app (eqVal V ψ)
                  (SetTheory.app (SetTheory.app (quotVal V ψ) A) R))
                  (SetTheory.app (SetTheory.app
                    (SetTheory.app (quotMkVal V ψ) A) R) a),
                SetTheory.app (SetTheory.app
                  (SetTheory.app (quotMkVal V ψ) A) R) b,
                1, SetTheory.app (SetTheory.app (quotVal V ψ) A) R,
                (fun _ => univ 0),
                ?_, ?_, eqVal_app₂_mem hQD hsA, hsB,
                fun _ _ => univ_mem_univ 0⟩
                all_goals try simp [interpExpr, Expr.instantiate1, updV,
                  hfindE', hvalE', hfindQ', hvalQ', hfindMk', hvalMk',
                  eqA, quotA, quotMkA, ConstantInfo.toConstantVal]
                all_goals try rfl
              · -- fibre-universe of the proof binder (annotation 0)
                refine ⟨SetTheory.app (SetTheory.app
                    (SetTheory.app (eqVal V ψ)
                      (SetTheory.app (SetTheory.app (quotVal V ψ) A) R))
                    (SetTheory.app (SetTheory.app
                      (SetTheory.app (quotMkVal V ψ) A) R) a))
                    (SetTheory.app (SetTheory.app
                      (SetTheory.app (quotMkVal V ψ) A) R) b), ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV, hfindE',
                    hvalE', hfindQ', hvalQ', hfindMk', hvalMk', eqA,
                    quotA, quotMkA, ConstantInfo.toConstantVal]
                  try rfl
                · rw [hEq3 R hRmem' a b hamem hbmem]
                  exact eqv_mem_univ _ _
          · -- fibre-universe of the `b` binder
            refine ⟨pi 0 (SetTheory.app (SetTheory.app R a) b) (fun _ =>
              SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ)
                (SetTheory.app (SetTheory.app (quotVal V ψ) A) R))
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (quotMkVal V ψ) A) R) a))
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (quotMkVal V ψ) A) R) b)), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindE',
                hvalE', hfindQ', hvalQ', hfindMk', hvalMk', eqA, quotA,
                quotMkA, ConstantInfo.toConstantVal, Level.eval]
              try rfl
            · exact hW R hRmem' a b hamem hbmem
        · -- fibre-universe of the `a` binder
          refine ⟨pi 0 A (fun b' =>
            pi 0 (SetTheory.app (SetTheory.app R a) b') fun _ =>
              SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ)
                (SetTheory.app (SetTheory.app (quotVal V ψ) A) R))
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (quotMkVal V ψ) A) R) a))
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (quotMkVal V ψ) A) R) b')), ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
              hfindQ', hvalQ', hfindMk', hvalMk', eqA, quotA, quotMkA,
              ConstantInfo.toConstantVal, Level.eval]
            try rfl
          · exact hB4 R hRmem' a hamem
      · -- fibre-universe of the `r` binder
        refine ⟨pi 0 A (fun a' => pi 0 A fun b' =>
          pi 0 (SetTheory.app (SetTheory.app R a') b') fun _ =>
            SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ)
              (SetTheory.app (SetTheory.app (quotVal V ψ) A) R))
              (SetTheory.app (SetTheory.app
                (SetTheory.app (quotMkVal V ψ) A) R) a'))
              (SetTheory.app (SetTheory.app
                (SetTheory.app (quotMkVal V ψ) A) R) b')), ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
            hfindQ', hvalQ', hfindMk', hvalMk', eqA, quotA, quotMkA,
            ConstantInfo.toConstantVal, Level.eval]
          try rfl
        · exact hA3 R hRmem'
  · -- fibre-universe of the `α` binder
    refine ⟨pi 0 (relSpace V (ψ uN) A) (fun R' =>
      pi 0 A fun a' => pi 0 A fun b' =>
        pi 0 (SetTheory.app (SetTheory.app R' a') b') fun _ =>
          SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ)
            (SetTheory.app (SetTheory.app (quotVal V ψ) A) R'))
            (SetTheory.app (SetTheory.app
              (SetTheory.app (quotMkVal V ψ) A) R') a'))
            (SetTheory.app (SetTheory.app
              (SetTheory.app (quotMkVal V ψ) A) R') b')), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
        hfindQ', hvalQ', hfindMk', hvalMk', eqA, quotA, quotMkA,
        ConstantInfo.toConstantVal, Level.eval, uN, relSpace,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · exact hT1

end Setlec
