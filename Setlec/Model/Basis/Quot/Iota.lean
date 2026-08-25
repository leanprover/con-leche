import Setlec.Model.BasisInstall
import Setlec.Model.Basis.Glue
import Setlec.Model.RuleFold

/-!
# `Quot.lift`/`Quot.ind` iota-rule semantics

The rule right-hand sides of the two pinned `Quot` eliminators: their
interpretations computed, the fold equations against the hand-written
values, and the claims packaging consumed by the installation step
(`quotLiftIota_claims` / `quotIndIota_claims`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-- The (annotated) rhs of `Quot.lift`'s single rule. -/
def quotLiftRhsA : Expr :=
  ((ConstantInfo.recRules quotLiftA).getD 0 default).rhs

/-- The (annotated) rhs of `Quot.ind`'s single rule. -/
def quotIndRhsA : Expr :=
  ((ConstantInfo.recRules quotIndA).getD 0 default).rhs

/-! The lift rhs's lam-tag evaluations (raw imax forms, innermost
first: `h`, `f`, `β`, `r`, `α`). -/

def qlH (u v : Nat) : Nat := if v = 0 then 0 else Nat.max u v
def qlF (u v : Nat) : Nat :=
  if qlH u v = 0 then 0 else Nat.max 0 (qlH u v)
def qlBI (u v : Nat) : Nat :=
  if qlF u v = 0 then 0 else Nat.max (qlH u v) (qlF u v)
def qlRI (u v : Nat) : Nat :=
  if qlBI u v = 0 then 0 else Nat.max (v + 1) (qlBI u v)
def qlAI (u v : Nat) : Nat :=
  if qlRI u v = 0 then 0
  else Nat.max (if Nat.max u 1 = 0 then 0 else Nat.max u (Nat.max u 1))
    (qlRI u v)

theorem qlF_eq (u v : Nat) : qlF u v = qlH u v := by
  unfold qlF qlH
  by_cases h : v = 0
  · simp [h]
  · simp only [if_neg h, if_neg (max_ne_zero_r' h)]
    exact Nat.zero_max _

theorem qlBI_eq (u v : Nat) : qlBI u v = qlH u v := by
  unfold qlBI
  rw [qlF_eq]
  unfold qlH
  by_cases h : v = 0
  · simp [h]
  · simp only [if_neg h, if_neg (max_ne_zero_r' h)]
    exact Nat.max_self _

theorem qlRI_eq (u v : Nat) :
    qlRI u v = if v = 0 then 0 else Nat.max (v + 1) (Nat.max u v) := by
  unfold qlRI
  rw [qlBI_eq]
  unfold qlH
  by_cases h : v = 0
  · simp [h]
  · simp only [if_neg h, if_neg (max_ne_zero_r' h)]

theorem qlAI_eq (u v : Nat) :
    qlAI u v = if v = 0 then 0
      else Nat.max (Nat.max u 1) (Nat.max (v + 1) (Nat.max u v)) := by
  unfold qlAI
  rw [qlRI_eq]
  by_cases h : v = 0
  · simp [h]
  · have h1 : Nat.max u 1 ≠ 0 := max_ne_zero_r' (by decide)
    simp only [if_neg h, if_neg (max_ne_zero_l (Nat.succ_ne_zero v)),
      if_neg h1, max_absorb_l']

theorem qlAI_eq' (u v : Nat) :
    qlAI u v = if qlRI u v = 0 then 0
      else Nat.max (Nat.max u 1) (qlRI u v) := by
  unfold qlAI
  rw [if_neg (max_ne_zero_r' (by decide)), max_absorb_l']

variable (V) in
/-- The interpreted invariance domain of the `Quot.lift` rule rhs (the
equation fibre in `Eq`-value form, at the substituted level). -/
private noncomputable def qlInvI (ψ : Name → Nat) (A R B f : V) : V :=
  pi 0 A fun a => pi 0 A fun b =>
    pi 0 (SetTheory.app (SetTheory.app R a) b) fun _ =>
      SetTheory.app (SetTheory.app (SetTheory.app
        (eqVal V (Level.substFn ψ [uN] [.param vN])) B)
        (SetTheory.app f a)) (SetTheory.app f b)

/-! The interpreted suffix towers of the lift rhs (opened at `α`, `r`,
`β`, `f`, `h`), and their pi counterparts. -/

variable (V) in
private noncomputable def qlRhsW5 (ψ : Name → Nat) (A f : V) : V :=
  SetTheory.lam (ψ vN) A fun a => SetTheory.app f a

variable (V) in
private noncomputable def qlRhsW4 (ψ : Name → Nat) (A R B f : V) : V :=
  SetTheory.lam (qlH (ψ uN) (ψ vN)) (qlInvI V ψ A R B f) fun _ =>
    qlRhsW5 V ψ A f

variable (V) in
private noncomputable def qlRhsW3 (ψ : Name → Nat) (A R B : V) : V :=
  SetTheory.lam (qlF (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B) fun f =>
    qlRhsW4 V ψ A R B f

variable (V) in
private noncomputable def qlRhsW2 (ψ : Name → Nat) (A R : V) : V :=
  SetTheory.lam (qlBI (ψ uN) (ψ vN)) (univ (ψ vN)) fun B =>
    qlRhsW3 V ψ A R B

variable (V) in
private noncomputable def qlRhsW1 (ψ : Name → Nat) (A : V) : V :=
  SetTheory.lam (qlRI (ψ uN) (ψ vN)) (relSpace V (ψ uN) A) fun R =>
    qlRhsW2 V ψ A R

variable (V) in
/-- The interpretation of the `Quot.lift` rule rhs, as a value (the
lam tags are the raw annotation evaluations; the invariance domain
carries the `Eq`-value form of the equation fibre). -/
noncomputable def quotLiftRhsVal (ψ : Name → Nat) : V :=
  SetTheory.lam (qlAI (ψ uN) (ψ vN)) (univ (ψ uN)) fun A =>
    qlRhsW1 V ψ A

/-- Interpretation of the `Quot.lift` rule rhs. -/
theorem interp_quotLift_rhs {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ') :
    interpClosed V cval env ψ quotLiftRhsA =
      some (quotLiftRhsVal V ψ) := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  simp only [interpClosed, quotLiftRhsA, quotLiftA, ConstantInfo.recRules,
    List.getD, List.getElem?_cons_zero, Option.getD_some,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindE', hvalE', eqA, List.length_cons, List.length_nil, reduceIte,
    Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, vN, relSpace,
    quotLiftRhsVal, qlRhsW1, qlRhsW2, qlRhsW3, qlRhsW4, qlRhsW5,
    qlInvI, qlAI, qlRI, qlBI, qlF, qlH,
    hfindE', hvalE', eqA, ConstantInfo.toConstantVal,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

variable (V) in
/-- The interpretation of the `Quot.ind` rule rhs, as a value (an
all-Prop λ-tower: every lam tag is `0`). -/
noncomputable def quotIndRhsVal (ψ : Name → Nat) : V :=
  SetTheory.lam 0 (univ (ψ uN)) fun A =>
    SetTheory.lam 0 (relSpace V (ψ uN) A) fun R =>
      SetTheory.lam 0
          (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
            fun _ => univ 0) fun B =>
        SetTheory.lam 0
            (pi 0 A fun a => SetTheory.app B
              (SetTheory.app (SetTheory.app (SetTheory.app
                (quotMkVal V ψ) A) R) a)) fun mk =>
          SetTheory.lam 0 A fun a => SetTheory.app mk a

/-- Interpretation of the `Quot.ind` rule rhs (an all-Prop λ-tower). -/
theorem interp_quotInd_rhs {cval : ConstVal V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ') :
    interpClosed V cval env ψ quotIndRhsA =
      some (quotIndRhsVal V ψ) := by
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA :=
    hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  have hfindMk' : env.find? ((Name.anonymous.str "Quot").str "mk") =
      some quotMkA := hfindMk
  have hvalMk' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "mk") ψ' = quotMkVal V ψ' :=
    hvalMk
  simp only [interpClosed, quotIndRhsA, quotIndA, ConstantInfo.recRules,
    List.getD, List.getElem?_cons_zero, Option.getD_some,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindQ', hvalQ', hfindMk', hvalMk', quotA, quotMkA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, vN, relSpace,
    quotIndRhsVal,
    hfindQ', hvalQ', hfindMk', hvalMk', quotA, quotMkA,
    ConstantInfo.toConstantVal,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-! ## Membership helpers for the quotient telescopes

Private copies of the value-application facts the claims proofs need
(the public counterparts live in the `Install` module). -/

private theorem relSpace_mem' {w : Nat} {A : V} (hA : A ∈ˢ univ w) :
    relSpace V w A ∈ˢ univ (Nat.max w 1) := by
  have hmem := pi_mem_univ (u := w) (v := Nat.max w 1)
    (B := fun _ => pi 1 A fun _ => univ 0) hA
    (fun x _ => pi_mem_univ (u := w) (v := 1) (B := fun _ => univ 0) hA
      (fun _ _ => univ_mem_univ 0))
  rwa [if_neg (max_ne_zero_r' (by decide)), max_absorb_l'] at hmem

private theorem rel_app₂_univ' {w : Nat} {A R a b : V} (hA : A ∈ˢ univ w)
    (hR : R ∈ˢ relSpace V w A) (ha : a ∈ˢ A) (hb : b ∈ˢ A) :
    SetTheory.app (SetTheory.app R a) b ∈ˢ univ 0 := by
  have hRa : SetTheory.app R a ∈ˢ pi 1 A fun _ => univ 0 :=
    app_mem hR ha (fun x _ => pi_mem_univ (u := w) (v := 1)
      (B := fun _ => univ 0) hA (fun _ _ => univ_mem_univ 0))
  exact app_mem hRa hb (fun _ _ => univ_mem_univ 0)

private theorem quotInvSpace_mem' {w : Nat} {A R f : V}
    (hA : A ∈ˢ univ w) (hR : R ∈ˢ relSpace V w A) :
    quotInvSpace V A R f ∈ˢ univ 0 := by
  refine pi_mem_univ (u := w) (v := 0) hA (fun a ha => ?_)
  refine pi_mem_univ (u := w) (v := 0) hA (fun b hb => ?_)
  exact pi_mem_univ (u := 0) (v := 0) (rel_app₂_univ' hA hR ha hb)
    (fun _ _ => eqv_mem_univ _ _)

/-- The invariance premise of the quotient laws, extracted from a
member of the interpreted invariance space. -/
private theorem inv_of_invSpace' {w : Nat} {A R f h : V}
    (hA : A ∈ˢ univ w) (hR : R ∈ˢ relSpace V w A)
    (hh : h ∈ˢ quotInvSpace V A R f) :
    ∀ a b, a ∈ˢ A → b ∈ˢ A →
      (∃ x, x ∈ˢ SetTheory.app (SetTheory.app R a) b) →
      SetTheory.app f a = SetTheory.app f b := by
  intro a b ha hb hex
  obtain ⟨x, hx⟩ := hex
  have h1 : SetTheory.app h a ∈ˢ pi 0 A fun b' =>
      pi 0 (SetTheory.app (SetTheory.app R a) b') fun _ =>
        eqv (SetTheory.app f a) (SetTheory.app f b') :=
    app_mem hh ha (fun a' ha' => pi_mem_univ (u := w) (v := 0) hA
      (fun b' hb' => pi_mem_univ (u := 0) (v := 0)
        (rel_app₂_univ' hA hR ha' hb') (fun _ _ => eqv_mem_univ _ _)))
  have h2 : SetTheory.app (SetTheory.app h a) b ∈ˢ
      pi 0 (SetTheory.app (SetTheory.app R a) b) fun _ =>
        eqv (SetTheory.app f a) (SetTheory.app f b) :=
    app_mem h1 hb (fun b' hb' => pi_mem_univ (u := 0) (v := 0)
      (rel_app₂_univ' hA hR ha hb') (fun _ _ => eqv_mem_univ _ _))
  have h3 : SetTheory.app (SetTheory.app (SetTheory.app h a) b) x ∈ˢ
      eqv (SetTheory.app f a) (SetTheory.app f b) :=
    app_mem h2 hx (fun _ _ => eqv_mem_univ _ _)
  exact mem_eqv h3

/-- The interpreted invariance domain of the rule rhs is the value's
invariance space (the `Eq`-value fibres collapse to `eqv`). -/
private theorem qlInvEq {A R B f : V} (hB : B ∈ˢ univ (ψ vN))
    (hf : f ∈ˢ pi (ψ vN) A fun _ => B) :
    qlInvI V ψ A R B f = quotInvSpace V A R f := by
  unfold qlInvI quotInvSpace
  refine pi_congr fun a ha => ?_
  refine pi_congr fun b hb => ?_
  refine pi_congr fun _ _ => ?_
  exact eqVal_app₃ (ψ := Level.substFn ψ [uN] [.param vN]) hB
    (app_mem hf ha fun _ _ => hB) (app_mem hf hb fun _ _ => hB)

/-- `quotMkVal` reads only its `u` parameter. -/
private theorem quotMkVal_lev {ψj : Name → Nat} (hlev : ψj uN = ψ uN) :
    (quotMkVal V ψj : V) = quotMkVal V ψ := by
  simp only [quotMkVal, hlev]

/-- The full application of `Quot.mk`'s value is the class former. -/
private theorem quotMkVal_app₃' {A R a : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R) a =
      quotClass (ψ uN) A R a := by
  by_cases hu : ψ uN = 0
  · have hset : quotSet (ψ uN) A R ∈ˢ univ 0 := by
      have hA0 : A ∈ˢ univ 0 := by
        rw [← hu]
        exact hA
      rw [hu]
      exact quotSet_mem_univ hA0
    rw [show (quotMkVal V ψ : V) = pt from by
        simp only [quotMkVal]
        refine lamC_of_forall fun A' hA' => ?_
        refine lamC_of_forall fun R' hR' => ?_
        refine lamC_of_forall fun a' ha' => ?_
        have hset' : quotSet (ψ uN) A' R' ∈ˢ univ 0 := by
          have hA0' : A' ∈ˢ univ 0 := hu ▸ hA'
          rw [hu]
          exact quotSet_mem_univ hA0'
        exact mem_univ_zero hset' (quotClass_mem ha'),
      app_pt, app_pt, app_pt]
    exact (mem_univ_zero hset (quotClass_mem ha)).symm
  · have hrel_u : ∀ X : V, X ∈ˢ univ (ψ uN) →
        relSpace V (ψ uN) X ∈ˢ univ (ψ uN) := by
      intro X hX
      have := relSpace_mem' hX
      rwa [show Nat.max (ψ uN) 1 = ψ uN from Nat.le_antisymm
        (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.one_le_iff_ne_zero.mpr hu⟩)
        (Nat.le_max_left _ _)] at this
    have hB2 : ∀ X : V, X ∈ˢ univ (ψ uN) → ∀ R' : V,
        (pi (ψ uN) X fun _ => quotSet (ψ uN) X R') ∈ˢ univ (ψ uN) := by
      intro X hX R'
      have := pi_mem_univ (u := ψ uN) (v := ψ uN)
        (B := fun _ => quotSet (ψ uN) X R') hX
        (fun _ _ => quotSet_mem_univ hX)
      rwa [if_neg hu,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
    have h1 : SetTheory.app (quotMkVal V ψ) A =
        SetTheory.lam (ψ uN) (relSpace V (ψ uN) A) fun R' =>
          SetTheory.lam (ψ uN) A fun a' => quotClass (ψ uN) A R' a' := by
      simp only [quotMkVal]
      refine app_lam hA
        (B := fun X => pi (ψ uN) (relSpace V (ψ uN) X) fun R' =>
          pi (ψ uN) X fun _ => quotSet (ψ uN) X R')
        (fun X _ => lam_mem (V := V) fun R' _ =>
          lam_mem (V := V) fun a' ha' => quotClass_mem ha')
        (fun X hX => ?_)
      have := pi_mem_univ (u := ψ uN) (v := ψ uN)
        (B := fun R' => pi (ψ uN) X fun _ => quotSet (ψ uN) X R')
        (hrel_u X hX) (fun R' _ => hB2 X hX R')
      rwa [if_neg hu,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
    have h2 : SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R =
        SetTheory.lam (ψ uN) A fun a' => quotClass (ψ uN) A R a' := by
      rw [h1]
      exact app_lam hR
        (B := fun R' => pi (ψ uN) A fun _ => quotSet (ψ uN) A R')
        (fun R' _ => lam_mem (V := V) fun a' ha' => quotClass_mem ha')
        (fun R' _ => hB2 A hA R')
    rw [h2]
    exact app_lam ha (B := fun _ => quotSet (ψ uN) A R)
      (fun a' ha' => quotClass_mem ha')
      (fun _ _ => quotSet_mem_univ hA)

/-! ## `Quot`/`Quot.mk` value applications (annotation-side helpers) -/

private theorem quotVal_fib_univ' {X : V} (hX : X ∈ˢ univ (ψ uN)) :
    (pi (ψ uN + 1) (relSpace V (ψ uN) X) fun _ => univ (ψ uN)) ∈ˢ
      univ (ψ uN + 1) := by
  have := pi_mem_univ (u := Nat.max (ψ uN) 1) (v := ψ uN + 1)
    (B := fun _ => univ (ψ uN)) (relSpace_mem' hX)
    (fun _ _ => univ_mem_univ (ψ uN))
  rwa [if_neg (Nat.succ_ne_zero _),
    show Nat.max (Nat.max (ψ uN) 1) (ψ uN + 1) = ψ uN + 1 from
      Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.le_succ _,
          Nat.succ_le_succ (Nat.zero_le _)⟩, Nat.le_refl _⟩)
        (Nat.le_max_right _ _)] at this

private theorem quotVal_mem' :
    (quotVal V ψ : V) ∈ˢ pi (ψ uN + 1) (univ (ψ uN)) fun X =>
      pi (ψ uN + 1) (relSpace V (ψ uN) X) fun _ => univ (ψ uN) := by
  simp only [quotVal]
  exact lam_mem (V := V)
    (B := fun X => pi (ψ uN + 1) (relSpace V (ψ uN) X) fun _ =>
      univ (ψ uN))
    fun X hX => lam_mem (V := V) (B := fun _ => univ (ψ uN))
      fun R _ => quotSet_mem_univ hX

private theorem quotVal_app₁' {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (quotVal V ψ) A =
      SetTheory.lam (ψ uN + 1) (relSpace V (ψ uN) A) fun R =>
        quotSet (ψ uN) A R := by
  simp only [quotVal]
  exact app_lam hA
    (B := fun X => pi (ψ uN + 1) (relSpace V (ψ uN) X) fun _ =>
      univ (ψ uN))
    (fun X hX => lam_mem (V := V) (B := fun _ => univ (ψ uN))
      fun R _ => quotSet_mem_univ hX)
    (fun X hX => quotVal_fib_univ' hX)

private theorem quotVal_app_mem' {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (quotVal V ψ) A ∈ˢ
      pi (ψ uN + 1) (relSpace V (ψ uN) A) fun _ => univ (ψ uN) := by
  rw [quotVal_app₁' hA]
  exact lam_mem (V := V) (B := fun _ => univ (ψ uN))
    fun R _ => quotSet_mem_univ hA

private theorem quotVal_app₂' {A R : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) :
    SetTheory.app (SetTheory.app (quotVal V ψ) A) R =
      quotSet (ψ uN) A R := by
  rw [quotVal_app₁' hA]
  exact app_lam hR (B := fun _ => univ (ψ uN))
    (fun R' _ => quotSet_mem_univ hA)
    (fun _ _ => univ_mem_univ (ψ uN))

private theorem quotMkD2_univ' {X : V} (hX : X ∈ˢ univ (ψ uN))
    {R : V} :
    (pi (ψ uN) X fun _ => quotSet (ψ uN) X R) ∈ˢ univ (ψ uN) := by
  have := pi_mem_univ (u := ψ uN) (v := ψ uN)
    (B := fun _ => quotSet (ψ uN) X R) hX
    (fun _ _ => quotSet_mem_univ hX)
  by_cases hu : ψ uN = 0
  · rw [hu] at this ⊢
    exact this
  · rwa [if_neg hu,
      show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this

private theorem quotMkD1_univ' {X : V} (hX : X ∈ˢ univ (ψ uN)) :
    (pi (ψ uN) (relSpace V (ψ uN) X) fun R =>
      pi (ψ uN) X fun _ => quotSet (ψ uN) X R) ∈ˢ univ (ψ uN) := by
  have := pi_mem_univ (u := Nat.max (ψ uN) 1) (v := ψ uN)
    (B := fun R => pi (ψ uN) X fun _ => quotSet (ψ uN) X R)
    (relSpace_mem' hX) (fun R _ => quotMkD2_univ' hX)
  by_cases hu : ψ uN = 0
  · rw [hu] at this ⊢
    exact this
  · rwa [if_neg hu,
      show Nat.max (Nat.max (ψ uN) 1) (ψ uN) = ψ uN from
        Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.le_refl _,
            Nat.one_le_iff_ne_zero.mpr hu⟩, Nat.le_refl _⟩)
          (Nat.le_max_right _ _)] at this

private theorem quotMkVal_mem' :
    (quotMkVal V ψ : V) ∈ˢ pi (ψ uN) (univ (ψ uN)) fun X =>
      pi (ψ uN) (relSpace V (ψ uN) X) fun R =>
        pi (ψ uN) X fun _ => quotSet (ψ uN) X R := by
  simp only [quotMkVal]
  exact lam_mem (V := V)
    (B := fun X => pi (ψ uN) (relSpace V (ψ uN) X) fun R =>
      pi (ψ uN) X fun _ => quotSet (ψ uN) X R)
    fun X hX => lam_mem (V := V)
      (B := fun R => pi (ψ uN) X fun _ => quotSet (ψ uN) X R)
      fun R _ => lam_mem (V := V) (B := fun _ => quotSet (ψ uN) X R)
        fun a ha => quotClass_mem ha

private theorem quotMkVal_app₁'' {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (quotMkVal V ψ) A =
      SetTheory.lam (ψ uN) (relSpace V (ψ uN) A) fun R =>
        SetTheory.lam (ψ uN) A fun a => quotClass (ψ uN) A R a := by
  simp only [quotMkVal]
  exact app_lam hA
    (B := fun X => pi (ψ uN) (relSpace V (ψ uN) X) fun R =>
      pi (ψ uN) X fun _ => quotSet (ψ uN) X R)
    (fun X hX => lam_mem (V := V)
      (B := fun R => pi (ψ uN) X fun _ => quotSet (ψ uN) X R)
      fun R _ => lam_mem (V := V) (B := fun _ => quotSet (ψ uN) X R)
        fun a ha => quotClass_mem ha)
    (fun X hX => quotMkD1_univ' hX)

private theorem quotMkVal_app_mem' {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (quotMkVal V ψ) A ∈ˢ
      pi (ψ uN) (relSpace V (ψ uN) A) fun R =>
        pi (ψ uN) A fun _ => quotSet (ψ uN) A R := by
  rw [quotMkVal_app₁'' hA]
  exact lam_mem (V := V)
    (B := fun R => pi (ψ uN) A fun _ => quotSet (ψ uN) A R)
    fun R _ => lam_mem (V := V) (B := fun _ => quotSet (ψ uN) A R)
      fun a ha => quotClass_mem ha

private theorem quotMkVal_app₂_mem' {A R : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) :
    SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R ∈ˢ
      pi (ψ uN) A fun _ => quotSet (ψ uN) A R := by
  rw [quotMkVal_app₁'' hA,
    show SetTheory.app (SetTheory.lam (ψ uN) (relSpace V (ψ uN) A)
        fun R' => SetTheory.lam (ψ uN) A fun a =>
          quotClass (ψ uN) A R' a) R =
      SetTheory.lam (ψ uN) A fun a => quotClass (ψ uN) A R a from
    app_lam hR
      (B := fun R' => pi (ψ uN) A fun _ => quotSet (ψ uN) A R')
      (fun R' _ => lam_mem (V := V) (B := fun _ => quotSet (ψ uN) A R')
        fun a ha => quotClass_mem ha)
      (fun R' _ => quotMkD2_univ' hA)]
  exact lam_mem (V := V) (B := fun _ => quotSet (ψ uN) A R)
    fun a ha => quotClass_mem ha

/-! ## The generic `Quot.lift` telescope

Away from the Prop collapse (`ψ vN ≠ 0`) both the hand-written
`quotLiftVal` and the interpreted rule rhs are instances of one
λ-tower, parametrized by the last binder's domain family `C` (a
function of the type and the relation) and its body `G`; the `qlD*`
are the matching pi-tower fibre families.  The value instantiates
`C A R := quotSet u A R`, `G A R f q := app (quotLift u v A R f) q`;
the rhs instantiates `C A R := A`, `G A R f a := app f a`. -/

variable (V) in
private noncomputable def qlD5 (v : Nat) (C : V → V → V)
    (A R B : V) : V :=
  pi v (C A R) fun _ => B

variable (V) in
private noncomputable def qlD4 (u v : Nat) (C : V → V → V)
    (A R B f : V) : V :=
  pi (Nat.max u v) (quotInvSpace V A R f) fun _ => qlD5 V v C A R B

variable (V) in
private noncomputable def qlD3 (u v : Nat) (C : V → V → V)
    (A R B : V) : V :=
  pi (Nat.max u v) (pi v A fun _ => B) fun f => qlD4 V u v C A R B f

variable (V) in
private noncomputable def qlD2 (u v : Nat) (C : V → V → V)
    (A R : V) : V :=
  pi (Nat.max u v) (univ v) fun B => qlD3 V u v C A R B

variable (V) in
private noncomputable def qlD1 (u v : Nat) (C : V → V → V) (A : V) : V :=
  pi (Nat.max (v + 1) (Nat.max u v)) (relSpace V u A) fun R =>
    qlD2 V u v C A R

variable (V) in
private noncomputable def qlL5 (v : Nat) (C : V → V → V)
    (G : V → V → V → V → V) (A R f : V) : V :=
  SetTheory.lam v (C A R) fun q => G A R f q

variable (V) in
private noncomputable def qlL4 (u v : Nat) (C : V → V → V)
    (G : V → V → V → V → V) (A R f : V) : V :=
  SetTheory.lam (Nat.max u v) (quotInvSpace V A R f) fun _ =>
    qlL5 V v C G A R f

variable (V) in
private noncomputable def qlL3 (u v : Nat) (C : V → V → V)
    (G : V → V → V → V → V) (A R B : V) : V :=
  SetTheory.lam (Nat.max u v) (pi v A fun _ => B) fun f =>
    qlL4 V u v C G A R f

variable (V) in
private noncomputable def qlL2 (u v : Nat) (C : V → V → V)
    (G : V → V → V → V → V) (A R : V) : V :=
  SetTheory.lam (Nat.max u v) (univ v) fun B => qlL3 V u v C G A R B

variable (V) in
private noncomputable def qlL1 (u v : Nat) (C : V → V → V)
    (G : V → V → V → V → V) (A : V) : V :=
  SetTheory.lam (Nat.max (v + 1) (Nat.max u v)) (relSpace V u A) fun R =>
    qlL2 V u v C G A R

variable (V) in
private noncomputable def qlVal (u v : Nat) (C : V → V → V)
    (G : V → V → V → V → V) : V :=
  SetTheory.lam (Nat.max (Nat.max u 1) (Nat.max (v + 1) (Nat.max u v)))
    (univ u) fun A => qlL1 V u v C G A

variable (V) in
/-- The last body lands in the codomain, over the whole telescope. -/
private abbrev QlG (u v : Nat) (C : V → V → V)
    (G : V → V → V → V → V) : Prop :=
  ∀ A R B f h q, A ∈ˢ univ u → R ∈ˢ relSpace V u A → B ∈ˢ univ v →
    f ∈ˢ pi v A (fun _ => B) → h ∈ˢ quotInvSpace V A R f →
    q ∈ˢ C A R → G A R f q ∈ˢ B

/-! Universe facts for the pi towers. -/

private theorem qlD5_univ {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {A R B : V} (hCAR : C A R ∈ˢ univ u) (hB : B ∈ˢ univ v) :
    qlD5 V v C A R B ∈ˢ univ (Nat.max u v) := by
  simp only [qlD5]
  have := pi_mem_univ (u := u) (v := v) (B := fun _ => B) hCAR
    (fun _ _ => hB)
  rwa [if_neg h0] at this

private theorem qlD4_univ {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {A R B f : V} (hA : A ∈ˢ univ u) (hR : R ∈ˢ relSpace V u A)
    (hCAR : C A R ∈ˢ univ u) (hB : B ∈ˢ univ v) :
    qlD4 V u v C A R B f ∈ˢ univ (Nat.max u v) := by
  simp only [qlD4]
  have := pi_mem_univ (u := 0) (v := Nat.max u v)
    (B := fun _ => qlD5 V v C A R B)
    (quotInvSpace_mem' (f := f) hA hR)
    (fun _ _ => qlD5_univ h0 hCAR hB)
  rwa [if_neg (max_ne_zero_r' h0),
    show Nat.max 0 (Nat.max u v) = Nat.max u v from Nat.zero_max _]
    at this

private theorem qlD3_univ {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {A R B : V} (hA : A ∈ˢ univ u) (hR : R ∈ˢ relSpace V u A)
    (hCAR : C A R ∈ˢ univ u) (hB : B ∈ˢ univ v) :
    qlD3 V u v C A R B ∈ˢ univ (Nat.max u v) := by
  simp only [qlD3]
  have hdom : (pi v A fun _ => B) ∈ˢ univ (Nat.max u v) := by
    have := pi_mem_univ (u := u) (v := v) (B := fun _ => B) hA
      (fun _ _ => hB)
    rwa [if_neg h0] at this
  have := pi_mem_univ (u := Nat.max u v) (v := Nat.max u v)
    (B := fun f => qlD4 V u v C A R B f) hdom
    (fun f _ => qlD4_univ h0 hA hR hCAR hB)
  rwa [if_neg (max_ne_zero_r' h0),
    show Nat.max (Nat.max u v) (Nat.max u v) = Nat.max u v from
      Nat.max_self _] at this

private theorem qlD2_univ {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {A R : V} (hA : A ∈ˢ univ u) (hR : R ∈ˢ relSpace V u A)
    (hCAR : C A R ∈ˢ univ u) :
    qlD2 V u v C A R ∈ˢ univ (Nat.max (v + 1) (Nat.max u v)) := by
  simp only [qlD2]
  have := pi_mem_univ (u := v + 1) (v := Nat.max u v)
    (B := fun B => qlD3 V u v C A R B) (univ_mem_univ v)
    (fun B hB => qlD3_univ h0 hA hR hCAR hB)
  rwa [if_neg (max_ne_zero_r' h0)] at this

private theorem qlD1_univ {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {A : V} (hA : A ∈ˢ univ u)
    (hC : ∀ R', R' ∈ˢ relSpace V u A → C A R' ∈ˢ univ u) :
    qlD1 V u v C A ∈ˢ
      univ (Nat.max (Nat.max u 1) (Nat.max (v + 1) (Nat.max u v))) := by
  simp only [qlD1]
  have := pi_mem_univ (u := Nat.max u 1)
    (v := Nat.max (v + 1) (Nat.max u v))
    (B := fun R => qlD2 V u v C A R) (relSpace_mem' hA)
    (fun R hR => qlD2_univ h0 hA hR (hC R hR))
  rwa [if_neg (max_ne_zero_l (Nat.succ_ne_zero v))] at this

/-! Membership of the lam towers in the pi towers. -/

private theorem qlL5_mem {v : Nat} {C : V → V → V}
    {G : V → V → V → V → V} {A R B f : V}
    (hGa : ∀ q, q ∈ˢ C A R → G A R f q ∈ˢ B) :
    qlL5 V v C G A R f ∈ˢ qlD5 V v C A R B := by
  simp only [qlL5, qlD5]
  exact lam_mem (V := V) (B := fun _ => B) hGa

private theorem qlL4_mem {u v : Nat} {C : V → V → V}
    {G : V → V → V → V → V} {A R B f : V} (hG : QlG V u v C G)
    (hA : A ∈ˢ univ u) (hR : R ∈ˢ relSpace V u A) (hB : B ∈ˢ univ v)
    (hf : f ∈ˢ pi v A fun _ => B) :
    qlL4 V u v C G A R f ∈ˢ qlD4 V u v C A R B f := by
  simp only [qlL4, qlD4]
  exact lam_mem (V := V) (B := fun _ => qlD5 V v C A R B)
    (fun h hh => qlL5_mem (fun q hq => hG A R B f h q hA hR hB hf hh hq))

private theorem qlL3_mem {u v : Nat} {C : V → V → V}
    {G : V → V → V → V → V} {A R B : V} (hG : QlG V u v C G)
    (hA : A ∈ˢ univ u) (hR : R ∈ˢ relSpace V u A) (hB : B ∈ˢ univ v) :
    qlL3 V u v C G A R B ∈ˢ qlD3 V u v C A R B := by
  simp only [qlL3, qlD3]
  exact lam_mem (V := V) (B := fun f => qlD4 V u v C A R B f)
    (fun f hf => qlL4_mem hG hA hR hB hf)

private theorem qlL2_mem {u v : Nat} {C : V → V → V}
    {G : V → V → V → V → V} {A R : V} (hG : QlG V u v C G)
    (hA : A ∈ˢ univ u) (hR : R ∈ˢ relSpace V u A) :
    qlL2 V u v C G A R ∈ˢ qlD2 V u v C A R := by
  simp only [qlL2, qlD2]
  exact lam_mem (V := V) (B := fun B => qlD3 V u v C A R B)
    (fun B hB => qlL3_mem hG hA hR hB)

private theorem qlL1_mem {u v : Nat} {C : V → V → V}
    {G : V → V → V → V → V} {A : V} (hG : QlG V u v C G)
    (hA : A ∈ˢ univ u) :
    qlL1 V u v C G A ∈ˢ qlD1 V u v C A := by
  simp only [qlL1, qlD1]
  exact lam_mem (V := V) (B := fun R => qlD2 V u v C A R)
    (fun R hR => qlL2_mem hG hA hR)

private theorem qlVal_mem {u v : Nat} {C : V → V → V}
    {G : V → V → V → V → V} (hG : QlG V u v C G) :
    (qlVal V u v C G : V) ∈ˢ
      pi (Nat.max (Nat.max u 1) (Nat.max (v + 1) (Nat.max u v)))
        (univ u) fun A => qlD1 V u v C A := by
  simp only [qlVal]
  exact lam_mem (V := V) (B := fun A => qlD1 V u v C A)
    (fun A hA => qlL1_mem hG hA)

/-! Application equations for the lam tower. -/

private theorem qlVal_app1 {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {G : V → V → V → V → V} (hG : QlG V u v C G)
    (hC : ∀ A R, A ∈ˢ univ u → R ∈ˢ relSpace V u A → C A R ∈ˢ univ u)
    {Av : V} (hA : Av ∈ˢ univ u) :
    SetTheory.app (qlVal V u v C G) Av = qlL1 V u v C G Av := by
  simp only [qlVal]
  exact app_lam (B := fun A => qlD1 V u v C A) hA
    (fun A hA' => qlL1_mem hG hA')
    (fun A hA' => qlD1_univ h0 hA' (fun R' hR' => hC A R' hA' hR'))

private theorem qlL1_app {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {G : V → V → V → V → V} (hG : QlG V u v C G)
    (hC : ∀ A R, A ∈ˢ univ u → R ∈ˢ relSpace V u A → C A R ∈ˢ univ u)
    {Av Rv : V} (hA : Av ∈ˢ univ u) (hR : Rv ∈ˢ relSpace V u Av) :
    SetTheory.app (qlL1 V u v C G Av) Rv = qlL2 V u v C G Av Rv := by
  simp only [qlL1]
  exact app_lam (B := fun R => qlD2 V u v C Av R) hR
    (fun R hR' => qlL2_mem hG hA hR')
    (fun R hR' => qlD2_univ h0 hA hR' (hC Av R hA hR'))

private theorem qlL2_app {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {G : V → V → V → V → V} (hG : QlG V u v C G)
    (hC : ∀ A R, A ∈ˢ univ u → R ∈ˢ relSpace V u A → C A R ∈ˢ univ u)
    {Av Rv Bv : V} (hA : Av ∈ˢ univ u) (hR : Rv ∈ˢ relSpace V u Av)
    (hB : Bv ∈ˢ univ v) :
    SetTheory.app (qlL2 V u v C G Av Rv) Bv = qlL3 V u v C G Av Rv Bv := by
  simp only [qlL2]
  exact app_lam (B := fun B => qlD3 V u v C Av Rv B) hB
    (fun B hB' => qlL3_mem hG hA hR hB')
    (fun B hB' => qlD3_univ h0 hA hR (hC Av Rv hA hR) hB')

private theorem qlL3_app {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {G : V → V → V → V → V} (hG : QlG V u v C G)
    (hC : ∀ A R, A ∈ˢ univ u → R ∈ˢ relSpace V u A → C A R ∈ˢ univ u)
    {Av Rv Bv fv : V} (hA : Av ∈ˢ univ u) (hR : Rv ∈ˢ relSpace V u Av)
    (hB : Bv ∈ˢ univ v) (hf : fv ∈ˢ pi v Av fun _ => Bv) :
    SetTheory.app (qlL3 V u v C G Av Rv Bv) fv =
      qlL4 V u v C G Av Rv fv := by
  simp only [qlL3]
  exact app_lam (B := fun f => qlD4 V u v C Av Rv Bv f) hf
    (fun f hf' => qlL4_mem hG hA hR hB hf')
    (fun f _ => qlD4_univ h0 hA hR (hC Av Rv hA hR) hB)

private theorem qlL4_app {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {G : V → V → V → V → V} (hG : QlG V u v C G)
    (hC : ∀ A R, A ∈ˢ univ u → R ∈ˢ relSpace V u A → C A R ∈ˢ univ u)
    {Av Rv Bv fv hv : V} (hA : Av ∈ˢ univ u)
    (hR : Rv ∈ˢ relSpace V u Av) (hB : Bv ∈ˢ univ v)
    (hf : fv ∈ˢ pi v Av fun _ => Bv)
    (hh : hv ∈ˢ quotInvSpace V Av Rv fv) :
    SetTheory.app (qlL4 V u v C G Av Rv fv) hv =
      qlL5 V v C G Av Rv fv := by
  simp only [qlL4]
  exact app_lam (B := fun _ => qlD5 V v C Av Rv Bv) hh
    (fun h hh' => qlL5_mem
      (fun q hq => hG Av Rv Bv fv h q hA hR hB hf hh' hq))
    (fun _ _ => qlD5_univ h0 (hC Av Rv hA hR) hB)

private theorem qlL5_app {v : Nat} {C : V → V → V}
    {G : V → V → V → V → V} {Av Rv fv qv Bv : V}
    (hq : qv ∈ˢ C Av Rv)
    (hGa : ∀ q, q ∈ˢ C Av Rv → G Av Rv fv q ∈ˢ Bv)
    (hB : Bv ∈ˢ univ v) :
    SetTheory.app (qlL5 V v C G Av Rv fv) qv = G Av Rv fv qv := by
  simp only [qlL5]
  exact app_lam (B := fun _ => Bv) hq hGa (fun _ _ => hB)

/-! The two instances of the tower. -/

/-- Away from the Prop collapse the hand-written value is the tower
instance at the quotient set and the lifted application. -/
private theorem quotLiftVal_eq_qlVal (h0 : ψ vN ≠ 0) :
    (quotLiftVal V ψ : V) = qlVal V (ψ uN) (ψ vN)
      (fun A R => quotSet (ψ uN) A R)
      (fun A R f q => SetTheory.app (quotLift (ψ uN) (ψ vN) A R f) q) := by
  simp only [quotLiftVal, qlVal, qlL1, qlL2, qlL3, qlL4, qlL5,
    if_neg h0, if_neg (max_ne_zero_l (Nat.succ_ne_zero (ψ vN)))]

/-- Away from the Prop collapse the interpreted rule rhs is the tower
instance at the type itself and plain application. -/
private theorem quotLiftRhsVal_eq_qlVal (h0 : ψ vN ≠ 0) :
    (quotLiftRhsVal V ψ : V) = qlVal V (ψ uN) (ψ vN)
      (fun A _ => A) (fun _ _ f a => SetTheory.app f a) := by
  have hq : qlH (ψ uN) (ψ vN) = Nat.max (ψ uN) (ψ vN) := by
    unfold qlH
    rw [if_neg h0]
  have hr : qlRI (ψ uN) (ψ vN) =
      Nat.max (ψ vN + 1) (Nat.max (ψ uN) (ψ vN)) := by
    rw [qlRI_eq, if_neg h0]
  have ha : qlAI (ψ uN) (ψ vN) = Nat.max (Nat.max (ψ uN) 1)
      (Nat.max (ψ vN + 1) (Nat.max (ψ uN) (ψ vN))) := by
    rw [qlAI_eq, if_neg h0]
  simp only [quotLiftRhsVal, qlRhsW1, qlRhsW2, qlRhsW3, qlRhsW4,
    qlRhsW5, qlVal, qlL1, qlL2, qlL3, qlL4, qlL5,
    qlF_eq, qlBI_eq, hq, hr, ha]
  refine lam_congr fun A _ => ?_
  refine lam_congr fun R _ => ?_
  refine lam_congr fun B hB' => ?_
  refine lam_congr fun f hf' => ?_
  rw [qlInvEq hB' hf']

/-! ## Annotation truthfulness: pi towers of the lift rhs suffixes -/

variable (V) in
private noncomputable def qlRhsP5 (ψ : Name → Nat) (A B : V) : V :=
  pi (ψ vN) A fun _ => B

variable (V) in
private noncomputable def qlRhsP4 (ψ : Name → Nat) (A R B f : V) : V :=
  pi (qlH (ψ uN) (ψ vN)) (qlInvI V ψ A R B f) fun _ =>
    qlRhsP5 V ψ A B

variable (V) in
private noncomputable def qlRhsP3 (ψ : Name → Nat) (A R B : V) : V :=
  pi (qlF (ψ uN) (ψ vN)) (qlRhsP5 V ψ A B) fun f =>
    qlRhsP4 V ψ A R B f

variable (V) in
private noncomputable def qlRhsP2 (ψ : Name → Nat) (A R : V) : V :=
  pi (qlBI (ψ uN) (ψ vN)) (univ (ψ vN)) fun B => qlRhsP3 V ψ A R B

variable (V) in
private noncomputable def qlRhsP1 (ψ : Name → Nat) (A : V) : V :=
  pi (qlRI (ψ uN) (ψ vN)) (relSpace V (ψ uN) A) fun R =>
    qlRhsP2 V ψ A R

private theorem qlRhsW5_mem {A B f : V} (hB : B ∈ˢ univ (ψ vN))
    (hf : f ∈ˢ pi (ψ vN) A fun _ => B) :
    qlRhsW5 V ψ A f ∈ˢ qlRhsP5 V ψ A B := by
  simp only [qlRhsW5, qlRhsP5]
  exact lam_mem (V := V) (B := fun _ => B)
    fun a ha => app_mem hf ha (fun _ _ => hB)

private theorem qlRhsW4_mem {A R B f : V} (hB : B ∈ˢ univ (ψ vN))
    (hf : f ∈ˢ pi (ψ vN) A fun _ => B) :
    qlRhsW4 V ψ A R B f ∈ˢ qlRhsP4 V ψ A R B f := by
  simp only [qlRhsW4, qlRhsP4]
  exact lam_mem (V := V) (B := fun _ => qlRhsP5 V ψ A B)
    fun _ _ => qlRhsW5_mem hB hf

private theorem qlRhsW3_mem {A R B : V} (hB : B ∈ˢ univ (ψ vN)) :
    qlRhsW3 V ψ A R B ∈ˢ qlRhsP3 V ψ A R B := by
  simp only [qlRhsW3, qlRhsP3, qlRhsP5]
  exact lam_mem (V := V) (B := fun f => qlRhsP4 V ψ A R B f)
    fun f hf => qlRhsW4_mem hB hf

private theorem qlRhsW2_mem {A R : V} :
    qlRhsW2 V ψ A R ∈ˢ qlRhsP2 V ψ A R := by
  simp only [qlRhsW2, qlRhsP2]
  exact lam_mem (V := V) (B := fun B => qlRhsP3 V ψ A R B)
    fun B hB => qlRhsW3_mem hB

private theorem qlRhsW1_mem {A : V} :
    qlRhsW1 V ψ A ∈ˢ qlRhsP1 V ψ A := by
  simp only [qlRhsW1, qlRhsP1]
  exact lam_mem (V := V) (B := fun R => qlRhsP2 V ψ A R)
    fun R _ => qlRhsW2_mem

private theorem qlRhsP5_univ {A B : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ univ (ψ vN)) :
    qlRhsP5 V ψ A B ∈ˢ univ (qlH (ψ uN) (ψ vN)) := by
  simp only [qlRhsP5]
  exact pi_mem_univ (u := ψ uN) (v := ψ vN) (B := fun _ => B) hA
    (fun _ _ => hB)

private theorem qlInvI_univ {A R B f : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) (hB : B ∈ˢ univ (ψ vN))
    (hf : f ∈ˢ pi (ψ vN) A fun _ => B) :
    qlInvI V ψ A R B f ∈ˢ univ 0 := by
  rw [qlInvEq hB hf]
  exact quotInvSpace_mem' hA hR

private theorem qlRhsP4_univ {A R B f : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) (hB : B ∈ˢ univ (ψ vN))
    (hf : f ∈ˢ pi (ψ vN) A fun _ => B) :
    qlRhsP4 V ψ A R B f ∈ˢ univ (qlF (ψ uN) (ψ vN)) := by
  simp only [qlRhsP4]
  exact pi_mem_univ (u := 0) (v := qlH (ψ uN) (ψ vN))
    (B := fun _ => qlRhsP5 V ψ A B) (qlInvI_univ hA hR hB hf)
    (fun _ _ => qlRhsP5_univ hA hB)

private theorem qlRhsP3_univ {A R B : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) (hB : B ∈ˢ univ (ψ vN)) :
    qlRhsP3 V ψ A R B ∈ˢ univ (qlBI (ψ uN) (ψ vN)) := by
  simp only [qlRhsP3]
  exact pi_mem_univ (u := qlH (ψ uN) (ψ vN)) (v := qlF (ψ uN) (ψ vN))
    (B := fun f => qlRhsP4 V ψ A R B f) (qlRhsP5_univ hA hB)
    (fun f hf => qlRhsP4_univ hA hR hB hf)

private theorem qlRhsP2_univ {A R : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) :
    qlRhsP2 V ψ A R ∈ˢ univ (qlRI (ψ uN) (ψ vN)) := by
  simp only [qlRhsP2]
  exact pi_mem_univ (u := ψ vN + 1) (v := qlBI (ψ uN) (ψ vN))
    (B := fun B => qlRhsP3 V ψ A R B) (univ_mem_univ (ψ vN))
    (fun B hB => qlRhsP3_univ hA hR hB)

private theorem qlRhsP1_univ {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    qlRhsP1 V ψ A ∈ˢ univ (qlAI (ψ uN) (ψ vN)) := by
  simp only [qlRhsP1]
  have := pi_mem_univ (u := Nat.max (ψ uN) 1)
    (v := qlRI (ψ uN) (ψ vN)) (B := fun R => qlRhsP2 V ψ A R)
    (relSpace_mem' hA) (fun R hR => qlRhsP2_univ hA hR)
  rwa [← qlAI_eq'] at this

/-- The `Quot.lift` rule rhs carries truthful annotations. -/
theorem annotOk_quotLift_rhs {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) quotLiftRhsA := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  simp only [quotLiftRhsA, quotLiftA, ConstantInfo.recRules, List.getD,
    List.getElem?_cons_zero, Option.getD_some, AnnotOk]
  refine ⟨trivial, qlAI (ψ uN) (ψ vN), ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · -- opened `λ (r : α → α → Prop), …`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, qlRI (ψ uN) (ψ vN), ?_⟩
    · -- AnnotOk of the relation domain
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
        Nat.max (ψ uN) 1, ?_⟩
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
      simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
        Option.some.injEq] at hSx
      subst hSx
      refine ⟨?_, ?_⟩
      · try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨(by simp [Expr.instantiate1, AnnotOk]), 1, ?_⟩
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
        refine ⟨trivial, ?_⟩
        exact ⟨univ 0,
          by simp [interpExpr, Expr.instantiate1, updV, Level.eval],
          univ_mem_univ 0⟩
      · refine ⟨pi 1 A fun _ => univ 0, ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV]
          try rfl
        · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
            hAmem (fun _ _ => univ_mem_univ 0)
    · intro R SR hSR hRmem
      simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
        Level.eval, Option.some.injEq] at hSR
      subst hSR
      have hRrel : R ∈ˢ relSpace V (ψ uN) A := hRmem
      refine ⟨?_, ?_⟩
      · -- opened `λ (β : Sort v), …`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨trivial, qlBI (ψ uN) (ψ vN), ?_⟩
        intro B SB hSB hBmem
        have hSB' : SB = univ (ψ vN) := by
          simp only [interpExpr, Expr.instantiate1, reduceIte,
            Level.eval, Option.some.injEq] at hSB
          rw [← hSB]
          rfl
        rw [hSB'] at hBmem
        refine ⟨?_, ?_⟩
        · -- opened `λ (f : α → β), …`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨?_, qlF (ψ uN) (ψ vN), ?_⟩
          · -- AnnotOk of `(a : α) → β`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
              ψ vN, ?_⟩
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
            refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
            exact ⟨B, by simp [interpExpr, Expr.instantiate1, updV],
              hBmem⟩
          · intro f Sf hSf hfmem
            simp [interpExpr, Expr.instantiate1, updV, Level.eval,
              Option.some.injEq] at hSf
            subst hSf
            have hfc : f ∈ˢ pi (ψ vN) A fun _ => B := hfmem
            have hfa : ∀ x, x ∈ˢ A → SetTheory.app f x ∈ˢ B :=
              fun x hx => app_mem hfc hx (fun _ _ => hBmem)
            refine ⟨?_, ?_⟩
            · -- opened `λ (h : invariance), …`
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨?_, qlH (ψ uN) (ψ vN), ?_⟩
              · -- AnnotOk of the invariance domain
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                  0, ?_⟩
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
                simp only [interpExpr, Expr.instantiate1, reduceIte,
                  updV, Option.some.injEq] at hSa
                subst hSa
                refine ⟨?_, ?_⟩
                · -- opened `∀ (b : α), r a b → Eq β (f a) (f b)`
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                    0, ?_⟩
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
                  simp only [interpExpr, Expr.instantiate1, reduceIte,
                    updV, Option.some.injEq] at hSb
                  subst hSb
                  refine ⟨?_, ?_⟩
                  · -- opened `r a b → Eq β (f a) (f b)`
                    try simp only [Expr.instantiate1, reduceIte,
                      AnnotOk]
                    refine ⟨?_, 0, ?_⟩
                    · -- AnnotOk of `r a b`
                      try simp only [Expr.instantiate1, reduceIte,
                        AnnotOk]
                      refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                          (by simp [Expr.instantiate1, AnnotOk]),
                          R, a, Nat.max (ψ uN) 1, A,
                          (fun _ => pi 1 A fun _ => univ 0),
                          (by simp [interpExpr, Expr.instantiate1,
                            updV]),
                          (by simp [interpExpr, Expr.instantiate1,
                            updV]),
                          hRrel, hamem, fun x _ =>
                            pi_mem_univ (u := ψ uN) (v := 1)
                              (B := fun _ => univ 0) hAmem
                              (fun _ _ => univ_mem_univ 0)⟩,
                        (by simp [Expr.instantiate1, AnnotOk]),
                        SetTheory.app R a, b, 1, A, (fun _ => univ 0),
                        (by simp [interpExpr, Expr.instantiate1,
                          updV]),
                        (by simp [interpExpr, Expr.instantiate1,
                          updV]),
                        ?_, hbmem, fun _ _ => univ_mem_univ 0⟩
                      exact app_mem hRrel hamem (fun x _ =>
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
                      intro w Sw _hSw _hwmem
                      refine ⟨?_, ?_⟩
                      · -- AnnotOk of `Eq β (f a) (f b)`
                        try simp only [Expr.instantiate1, reduceIte,
                          AnnotOk]
                        refine ⟨⟨⟨(by simp [Expr.instantiate1,
                              AnnotOk]),
                            (by simp [Expr.instantiate1, AnnotOk]),
                            eqVal V (Level.substFn ψ [uN]
                              [Level.param vN]),
                            B, Nat.max (ψ vN) (Nat.max (ψ vN) 1),
                            univ (ψ vN),
                            (fun X => pi (Nat.max (ψ vN) 1) X fun _ =>
                              pi 1 X fun _ => univ 0),
                            ?_, ?_,
                            eqVal_mem (ψ := Level.substFn ψ [uN]
                              [Level.param vN]),
                            hBmem,
                            fun X hX => eq_fibre_mem
                              (ψ := Level.substFn ψ [uN]
                                [Level.param vN]) hX⟩,
                          ⟨(by simp [Expr.instantiate1, AnnotOk]),
                            (by simp [Expr.instantiate1, AnnotOk]),
                            f, a, ψ vN, A, (fun _ => B),
                            (by simp [interpExpr, Expr.instantiate1,
                              updV]),
                            (by simp [interpExpr, Expr.instantiate1,
                              updV]),
                            hfc, hamem, fun _ _ => hBmem⟩,
                          SetTheory.app (eqVal V (Level.substFn ψ [uN]
                            [Level.param vN])) B,
                          SetTheory.app f a, Nat.max (ψ vN) 1, B,
                          (fun _ => pi 1 B fun _ => univ 0),
                          ?_, ?_,
                          eqVal_app_mem (ψ := Level.substFn ψ [uN]
                            [Level.param vN]) hBmem,
                          hfa a hamem, fun y _ =>
                            pi_mem_univ (u := ψ vN) (v := 1)
                              (B := fun _ => univ 0) hBmem
                              (fun _ _ => univ_mem_univ 0)⟩,
                          ⟨(by simp [Expr.instantiate1, AnnotOk]),
                            (by simp [Expr.instantiate1, AnnotOk]),
                            f, b, ψ vN, A, (fun _ => B),
                            (by simp [interpExpr, Expr.instantiate1,
                              updV]),
                            (by simp [interpExpr, Expr.instantiate1,
                              updV]),
                            hfc, hbmem, fun _ _ => hBmem⟩,
                          SetTheory.app (SetTheory.app (eqVal V
                            (Level.substFn ψ [uN] [Level.param vN]))
                            B) (SetTheory.app f a),
                          SetTheory.app f b, 1, B, (fun _ => univ 0),
                          ?_, ?_,
                          eqVal_app₂_mem (ψ := Level.substFn ψ [uN]
                            [Level.param vN]) hBmem (hfa a hamem),
                          hfa b hbmem, fun _ _ => univ_mem_univ 0⟩
                        · simp [interpExpr, Expr.instantiate1, updV,
                            uN, vN, hfindE', hvalE', eqA,
                            ConstantInfo.toConstantVal]
                          try rfl
                        · simp [interpExpr, Expr.instantiate1, updV]
                        · simp [interpExpr, Expr.instantiate1, updV,
                            uN, vN, hfindE', hvalE', eqA,
                            ConstantInfo.toConstantVal]
                          try rfl
                        · simp [interpExpr, Expr.instantiate1, updV]
                        · simp [interpExpr, Expr.instantiate1, updV,
                            uN, vN, hfindE', hvalE', eqA,
                            ConstantInfo.toConstantVal]
                          try rfl
                        · simp [interpExpr, Expr.instantiate1, updV]
                      · -- fibre of the `r a b` binder (cod `0`)
                        refine ⟨SetTheory.app (SetTheory.app
                          (SetTheory.app (eqVal V (Level.substFn ψ
                            [uN] [Level.param vN])) B)
                          (SetTheory.app f a)) (SetTheory.app f b),
                          ?_, ?_⟩
                        · simp [interpExpr, Expr.instantiate1, updV,
                            uN, vN, hfindE', hvalE', eqA,
                            ConstantInfo.toConstantVal]
                          try rfl
                        · rw [eqVal_app₃ (ψ := Level.substFn ψ [uN]
                            [Level.param vN]) hBmem (hfa a hamem)
                            (hfa b hbmem)]
                          exact eqv_mem_univ _ _
                  · -- fibre of the `b` binder (cod `imax 0 0`)
                    refine ⟨pi 0 (SetTheory.app (SetTheory.app R a) b)
                      fun _ => SetTheory.app (SetTheory.app
                        (SetTheory.app (eqVal V (Level.substFn ψ [uN]
                          [Level.param vN])) B) (SetTheory.app f a))
                        (SetTheory.app f b), ?_, ?_⟩
                    · simp [interpExpr, Expr.instantiate1, updV, uN,
                        vN, hfindE', hvalE', eqA,
                        ConstantInfo.toConstantVal]
                      try rfl
                    · refine pi_mem_univ (u := 0) (v := 0)
                        (rel_app₂_univ' hAmem hRrel hamem hbmem)
                        (fun x _ => ?_)
                      rw [eqVal_app₃ (ψ := Level.substFn ψ [uN]
                        [Level.param vN]) hBmem (hfa a hamem)
                        (hfa b hbmem)]
                      exact eqv_mem_univ _ _
                · -- fibre of the `a` binder (cod `imax u (imax 0 0)`)
                  refine ⟨pi 0 A fun b =>
                    pi 0 (SetTheory.app (SetTheory.app R a) b) fun _ =>
                      SetTheory.app (SetTheory.app (SetTheory.app
                        (eqVal V (Level.substFn ψ [uN]
                          [Level.param vN])) B) (SetTheory.app f a))
                        (SetTheory.app f b), ?_, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV, uN, vN,
                      hfindE', hvalE', eqA, ConstantInfo.toConstantVal]
                    try rfl
                  · refine pi_mem_univ (u := ψ uN) (v := 0) hAmem
                      (fun b hb => ?_)
                    refine pi_mem_univ (u := 0) (v := 0)
                      (rel_app₂_univ' hAmem hRrel hamem hb)
                      (fun x _ => ?_)
                    rw [eqVal_app₃ (ψ := Level.substFn ψ [uN]
                      [Level.param vN]) hBmem (hfa a hamem)
                      (hfa b hb)]
                    exact eqv_mem_univ _ _
              · intro h Sh _hSh _hhmem
                refine ⟨?_, ?_⟩
                · -- opened `λ (a : α), f a`
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                    ψ vN, ?_⟩
                  intro a Sa hSa hamem
                  simp only [interpExpr, Expr.instantiate1, reduceIte,
                    updV, Option.some.injEq] at hSa
                  subst hSa
                  refine ⟨?_, ?_⟩
                  · -- AnnotOk of `f a`
                    try simp only [Expr.instantiate1, reduceIte,
                      AnnotOk]
                    exact ⟨(by simp [Expr.instantiate1, AnnotOk]),
                      (by simp [Expr.instantiate1, AnnotOk]),
                      f, a, ψ vN, A, (fun _ => B),
                      (by simp [interpExpr, Expr.instantiate1, updV]),
                      (by simp [interpExpr, Expr.instantiate1, updV]),
                      hfc, hamem, fun _ _ => hBmem⟩
                  · refine ⟨SetTheory.app f a, B, ?_, ?_, ?_⟩
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · exact hfa a hamem
                    · exact hBmem
                · -- fibre of the `h` binder
                  refine ⟨qlRhsW5 V ψ A f, qlRhsP5 V ψ A B, ?_, ?_, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV, uN, vN,
                      qlRhsW5]
                    try rfl
                  · exact qlRhsW5_mem hBmem hfc
                  · exact qlRhsP5_univ hAmem hBmem
            · -- fibre of the `f` binder
              refine ⟨qlRhsW4 V ψ A R B f, qlRhsP4 V ψ A R B f,
                ?_, ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV, uN, vN,
                  qlRhsW4, qlRhsW5, qlInvI, qlH, hfindE', hvalE', eqA,
                  ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · exact qlRhsW4_mem hBmem hfc
              · exact qlRhsP4_univ hAmem hRrel hBmem hfc
        · -- fibre of the `β` binder
          refine ⟨qlRhsW3 V ψ A R B, qlRhsP3 V ψ A R B, ?_, ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, uN, vN,
              qlRhsW3, qlRhsW4, qlRhsW5, qlInvI, qlH, qlF, hfindE',
              hvalE', eqA, ConstantInfo.toConstantVal,
              -ite_eq_left_iff, -ite_eq_right_iff,
              -Nat.max_eq_zero_iff]
            try rfl
          · exact qlRhsW3_mem hBmem
          · exact qlRhsP3_univ hAmem hRrel hBmem
      · -- fibre of the `r` binder
        refine ⟨qlRhsW2 V ψ A R, qlRhsP2 V ψ A R, ?_, ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, uN, vN, qlRhsW2,
            qlRhsW3, qlRhsW4, qlRhsW5, qlInvI, qlH, qlF, qlBI,
            hfindE', hvalE', eqA, ConstantInfo.toConstantVal,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · exact qlRhsW2_mem
        · exact qlRhsP2_univ hAmem hRrel
  · -- fibre of the `α` binder
    refine ⟨qlRhsW1 V ψ A, qlRhsP1 V ψ A, ?_, ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, uN, vN, relSpace,
        qlRhsW1, qlRhsW2, qlRhsW3, qlRhsW4, qlRhsW5, qlInvI, qlH, qlF,
        qlBI, qlRI, hfindE', hvalE', eqA, ConstantInfo.toConstantVal,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · exact qlRhsW1_mem
    · exact qlRhsP1_univ hAmem

/-- The `Quot.ind` rule rhs carries truthful annotations. -/
theorem annotOk_quotInd_rhs {cval : ConstVal V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) quotIndRhsA := by
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA :=
    hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  have hfindMk' : env.find? ((Name.anonymous.str "Quot").str "mk") =
      some quotMkA := hfindMk
  have hvalMk' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "mk") ψ' = quotMkVal V ψ' :=
    hvalMk
  simp only [quotIndRhsA, quotIndA, ConstantInfo.recRules, List.getD,
    List.getElem?_cons_zero, Option.getD_some, AnnotOk]
  refine ⟨trivial, 0, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · -- opened `λ (r : α → α → Prop), …`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, 0, ?_⟩
    · -- AnnotOk of the relation domain
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
        Nat.max (ψ uN) 1, ?_⟩
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
      simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
        Option.some.injEq] at hSx
      subst hSx
      refine ⟨?_, ?_⟩
      · -- inner `α → Prop`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨(by simp [Expr.instantiate1, AnnotOk]), 1, ?_⟩
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
        refine ⟨trivial, ?_⟩
        exact ⟨univ 0,
          by simp [interpExpr, Expr.instantiate1, updV, Level.eval],
          univ_mem_univ 0⟩
      · refine ⟨pi 1 A fun _ => univ 0, ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV]
          try rfl
        · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
            hAmem (fun _ _ => univ_mem_univ 0)
    · intro R SR hSR hRmem
      simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
        Level.eval, Option.some.injEq] at hSR
      subst hSR
      have hRrel : R ∈ˢ relSpace V (ψ uN) A := hRmem
      refine ⟨?_, ?_⟩
      · -- opened `λ (β : Quot α r → Prop), …`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨?_, 0, ?_⟩
        · -- AnnotOk of the motive domain `Quot α r → Prop`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
              quotVal V ψ, A, ψ uN + 1, univ (ψ uN),
              (fun X => pi (ψ uN + 1) (relSpace V (ψ uN) X) fun _ =>
                univ (ψ uN)),
              ?_, ?_, quotVal_mem', hAmem,
              fun X hX => quotVal_fib_univ' hX⟩,
            (by simp [Expr.instantiate1, AnnotOk]),
              SetTheory.app (quotVal V ψ) A, R, ψ uN + 1,
              relSpace V (ψ uN) A, (fun _ => univ (ψ uN)),
              ?_, ?_, quotVal_app_mem' hAmem, hRrel,
              fun _ _ => univ_mem_univ (ψ uN)⟩,
            1, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
              quotA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
          · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
              quotA, ConstantInfo.toConstantVal]
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
            intro x Sx hSx hxmem
            refine ⟨trivial, ?_⟩
            exact ⟨univ 0,
              by simp [interpExpr, Expr.instantiate1, updV, Level.eval],
              univ_mem_univ 0⟩
        · intro B SB hSB hBmem
          simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
            quotA, ConstantInfo.toConstantVal, Level.eval,
            -ite_eq_left_iff, -ite_eq_right_iff,
            -Nat.max_eq_zero_iff] at hSB
          subst hSB
          have hBq : B ∈ˢ pi 1 (quotSet (ψ uN) A R) fun _ => univ 0 := by
            rw [← quotVal_app₂' hAmem hRrel]
            exact hBmem
          refine ⟨?_, ?_⟩
          · -- opened `λ (mk : ∀ a, β (Quot.mk α r a)), …`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨?_, 0, ?_⟩
            · -- AnnotOk of the mk domain
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                0, ?_⟩
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
              simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
                Option.some.injEq] at hSa
              subst hSa
              refine ⟨?_, ?_⟩
              · -- AnnotOk of `β (Quot.mk α r a)`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                  ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                    quotMkVal V ψ, A, ψ uN, univ (ψ uN),
                    (fun X => pi (ψ uN) (relSpace V (ψ uN) X) fun R' =>
                      pi (ψ uN) X fun _ => quotSet (ψ uN) X R'),
                    ?_, ?_, quotMkVal_mem', hAmem,
                    fun X hX => quotMkD1_univ' hX⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                    SetTheory.app (quotMkVal V ψ) A, R, ψ uN,
                    relSpace V (ψ uN) A,
                    (fun R' => pi (ψ uN) A fun _ => quotSet (ψ uN) A R'),
                    ?_, ?_, quotMkVal_app_mem' hAmem, hRrel,
                    fun R' _ => quotMkD2_univ' hAmem⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                    SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R, a,
                    ψ uN, A, (fun _ => quotSet (ψ uN) A R),
                    ?_, ?_, quotMkVal_app₂_mem' hAmem hRrel, hamem,
                    fun _ _ => quotSet_mem_univ hAmem⟩,
                  B, SetTheory.app (SetTheory.app (SetTheory.app
                    (quotMkVal V ψ) A) R) a, 1,
                  quotSet (ψ uN) A R, (fun _ => univ 0),
                  ?_, ?_, hBq, ?_, fun _ _ => univ_mem_univ 0⟩
                · simp [interpExpr, Expr.instantiate1, updV, hfindMk',
                    hvalMk', quotMkA, ConstantInfo.toConstantVal]
                  try rfl
                · simp [interpExpr, Expr.instantiate1, updV]
                · simp [interpExpr, Expr.instantiate1, updV, hfindMk',
                    hvalMk', quotMkA, ConstantInfo.toConstantVal]
                  try rfl
                · simp [interpExpr, Expr.instantiate1, updV]
                · simp [interpExpr, Expr.instantiate1, updV, hfindMk',
                    hvalMk', quotMkA, ConstantInfo.toConstantVal]
                  try rfl
                · simp [interpExpr, Expr.instantiate1, updV]
                · simp [interpExpr, Expr.instantiate1, updV]
                · simp [interpExpr, Expr.instantiate1, updV, hfindMk',
                    hvalMk', quotMkA, ConstantInfo.toConstantVal]
                  try rfl
                · rw [quotMkVal_app₃' hAmem hRrel hamem]
                  exact quotClass_mem hamem
              · refine ⟨SetTheory.app B (SetTheory.app (SetTheory.app
                  (SetTheory.app (quotMkVal V ψ) A) R) a), ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV, hfindMk',
                    hvalMk', quotMkA, ConstantInfo.toConstantVal]
                  try rfl
                · rw [quotMkVal_app₃' hAmem hRrel hamem]
                  exact app_mem hBq (quotClass_mem hamem)
                    (fun _ _ => univ_mem_univ 0)
            · intro mk Smk hSmk hmkmem
              simp [interpExpr, Expr.instantiate1, updV, hfindMk',
                hvalMk', quotMkA, ConstantInfo.toConstantVal,
                -ite_eq_left_iff, -ite_eq_right_iff,
                -Nat.max_eq_zero_iff] at hSmk
              subst hSmk
              have hmkfib : ∀ x, x ∈ˢ A →
                  SetTheory.app B (SetTheory.app (SetTheory.app
                    (SetTheory.app (quotMkVal V ψ) A) R) x) ∈ˢ
                    univ 0 := by
                intro x hx
                rw [quotMkVal_app₃' hAmem hRrel hx]
                exact app_mem hBq (quotClass_mem hx)
                  (fun _ _ => univ_mem_univ 0)
              refine ⟨?_, ?_⟩
              · -- opened `λ (a : α), mk a`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                  0, ?_⟩
                intro a Sa hSa hamem
                simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
                  Option.some.injEq] at hSa
                subst hSa
                refine ⟨?_, ?_⟩
                · -- AnnotOk of `mk a`
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                    (by simp [Expr.instantiate1, AnnotOk]), mk, a, 0, A,
                    (fun x => SetTheory.app B (SetTheory.app
                      (SetTheory.app (SetTheory.app (quotMkVal V ψ) A)
                        R) x)),
                    ?_, ?_, hmkmem, hamem, fun x hx => hmkfib x hx⟩
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV]
                · refine ⟨SetTheory.app mk a,
                    SetTheory.app B (SetTheory.app (SetTheory.app
                      (SetTheory.app (quotMkVal V ψ) A) R) a),
                    ?_, ?_, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · exact app_mem hmkmem hamem (fun x hx => hmkfib x hx)
                  · exact hmkfib a hamem
              · refine ⟨SetTheory.lam 0 A fun a => SetTheory.app mk a,
                  unitSet, ?_, ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV]
                  try rfl
                · rw [show (SetTheory.lam 0 A fun a =>
                      SetTheory.app mk a) = (pt : V) from
                    lamC_of_forall fun a ha =>
                      mem_univ_zero (hmkfib a ha)
                        (app_mem_piC hmkmem ha)]
                  exact pt_mem_unitSet
                · exact unitSet_mem_univ 0
          · refine ⟨SetTheory.lam 0
              (pi 0 A fun a => SetTheory.app B (SetTheory.app
                (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R) a))
              fun mk => SetTheory.lam 0 A fun a => SetTheory.app mk a,
              unitSet, ?_, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindMk',
                hvalMk', quotMkA, ConstantInfo.toConstantVal,
                -ite_eq_left_iff, -ite_eq_right_iff,
                -Nat.max_eq_zero_iff]
              try rfl
            · have hmkfib0 : ∀ x, x ∈ˢ A →
                  SetTheory.app B (SetTheory.app (SetTheory.app
                    (SetTheory.app (quotMkVal V ψ) A) R) x) ∈ˢ
                    univ 0 := by
                intro x hx
                rw [quotMkVal_app₃' hAmem hRrel hx]
                exact app_mem hBq (quotClass_mem hx)
                  (fun _ _ => univ_mem_univ 0)
              rw [show (SetTheory.lam 0
                  (pi 0 A fun a => SetTheory.app B (SetTheory.app
                    (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R)
                      a))
                  fun mk => SetTheory.lam 0 A fun a =>
                    SetTheory.app mk a) = (pt : V) from by
                refine lamC_of_forall fun mk hmk => ?_
                exact lamC_of_forall fun a ha =>
                  mem_univ_zero (hmkfib0 a ha) (app_mem_piC hmk ha)]
              exact pt_mem_unitSet
            · exact unitSet_mem_univ 0
      · refine ⟨SetTheory.lam 0
          (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
            fun _ => univ 0)
          fun B => SetTheory.lam 0
            (pi 0 A fun a => SetTheory.app B (SetTheory.app
              (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R) a))
            fun mk => SetTheory.lam 0 A fun a => SetTheory.app mk a,
          unitSet, ?_, ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ',
            hfindMk', hvalMk', quotA, quotMkA,
            ConstantInfo.toConstantVal,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · rw [show (SetTheory.lam 0
              (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
                fun _ => univ 0)
              fun B => SetTheory.lam 0
                (pi 0 A fun a => SetTheory.app B (SetTheory.app
                  (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R)
                    a))
                fun mk => SetTheory.lam 0 A fun a =>
                  SetTheory.app mk a) = (pt : V) from by
            refine lamC_of_forall fun B hB' => ?_
            have hBq' : B ∈ˢ pi 1 (quotSet (ψ uN) A R)
                (fun _ => univ 0) := by
              rw [← quotVal_app₂' hAmem hRrel]
              exact hB'
            refine lamC_of_forall fun mk hmk => ?_
            refine lamC_of_forall fun a ha => ?_
            have hfib : SetTheory.app B (SetTheory.app (SetTheory.app
                (SetTheory.app (quotMkVal V ψ) A) R) a) ∈ˢ univ 0 := by
              rw [quotMkVal_app₃' hAmem hRrel ha]
              exact app_mem hBq' (quotClass_mem ha)
                (fun _ _ => univ_mem_univ 0)
            exact mem_univ_zero hfib (app_mem_piC hmk ha)]
          exact pt_mem_unitSet
        · exact unitSet_mem_univ 0
  · refine ⟨SetTheory.lam 0 (relSpace V (ψ uN) A)
      fun R => SetTheory.lam 0
        (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
          fun _ => univ 0)
        fun B => SetTheory.lam 0
          (pi 0 A fun a => SetTheory.app B (SetTheory.app
            (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R) a))
          fun mk => SetTheory.lam 0 A fun a => SetTheory.app mk a,
      unitSet, ?_, ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, relSpace, hfindQ',
        hvalQ', hfindMk', hvalMk', quotA, quotMkA,
        ConstantInfo.toConstantVal,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · rw [show (SetTheory.lam 0 (relSpace V (ψ uN) A)
          fun R => SetTheory.lam 0
            (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
              fun _ => univ 0)
            fun B => SetTheory.lam 0
              (pi 0 A fun a => SetTheory.app B (SetTheory.app
                (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R) a))
              fun mk => SetTheory.lam 0 A fun a =>
                SetTheory.app mk a) = (pt : V) from by
        refine lamC_of_forall fun R hR' => ?_
        refine lamC_of_forall fun B hB' => ?_
        have hBq' : B ∈ˢ pi 1 (quotSet (ψ uN) A R)
            (fun _ => univ 0) := by
          rw [← quotVal_app₂' hAmem hR']
          exact hB'
        refine lamC_of_forall fun mk hmk => ?_
        refine lamC_of_forall fun a ha => ?_
        have hfib : SetTheory.app B (SetTheory.app (SetTheory.app
            (SetTheory.app (quotMkVal V ψ) A) R) a) ∈ˢ univ 0 := by
          rw [quotMkVal_app₃' hAmem hR' ha]
          exact app_mem hBq' (quotClass_mem ha)
            (fun _ _ => univ_mem_univ 0)
        exact mem_univ_zero hfib (app_mem_piC hmk ha)]
      exact pt_mem_unitSet
    · exact unitSet_mem_univ 0

/-! ## `RecRulesOk` clauses: the canonical frame components -/

/-- The `α` frame variable (shared by the two eliminators). -/
def qFrA : Expr :=
  .fvar 0 (Name.anonymous.str "α") (.sort (.param (Name.anonymous.str "u")))

/-- The relation annotation. -/
def qFrTyR : Expr :=
  .forallE Name.anonymous qFrA
    (.forallE Name.anonymous qFrA (.sort .zero)
      ⟨.default, some (.succ .zero)⟩)
    ⟨.default, some (.imax (.param (Name.anonymous.str "u")) (.succ .zero))⟩

/-- The relation frame variable. -/
def qFrR : Expr := .fvar 1 (Name.anonymous.str "r") qFrTyR

/-- The `Quot.mk` head. -/
def qFrMkC : Expr :=
  .const ((Name.anonymous.str "Quot").str "mk")
    [.param (Name.anonymous.str "u")]

/-- The `β` frame variable of `Quot.lift`. -/
def qlFrB : Expr :=
  .fvar 2 (Name.anonymous.str "β") (.sort (.param (Name.anonymous.str "v")))

/-- The function annotation of `Quot.lift`. -/
def qlFrTyF : Expr :=
  .forallE (Name.anonymous.str "a") qFrA qlFrB
    ⟨.default, some (.param (Name.anonymous.str "v"))⟩

/-- The function frame variable of `Quot.lift`. -/
def qlFrF : Expr := .fvar 3 (Name.anonymous.str "f") qlFrTyF

/-- The invariance annotation of `Quot.lift`. -/
def qlFrTyH : Expr :=
  .forallE (Name.anonymous.str "a") qFrA
    (.forallE (Name.anonymous.str "b") qFrA
      (.forallE (Name.anonymous.str "a")
        (.app (.app qFrR (.bvar 1)) (.bvar 0))
        (.app (.app (.app (.const (Name.anonymous.str "Eq")
            [.param (Name.anonymous.str "v")]) qlFrB)
          (.app qlFrF (.bvar 2))) (.app qlFrF (.bvar 1)))
        ⟨.default, some .zero⟩)
      ⟨.default, some (.imax .zero .zero)⟩)
    ⟨.default, some (.imax (.param (Name.anonymous.str "u"))
      (.imax .zero .zero))⟩

/-- The invariance frame variable of `Quot.lift`. -/
def qlFrH : Expr := .fvar 4 (Name.anonymous.str "a") qlFrTyH

/-- The field frame variable of `Quot.lift`. -/
def qlFrq : Expr := .fvar 5 (Name.anonymous.str "a") qFrA

/-- The `Quot.lift` head. -/
def qlFrRec : Expr :=
  .const ((Name.anonymous.str "Quot").str "lift")
    [.param (Name.anonymous.str "u"), .param (Name.anonymous.str "v")]

/-- The motive frame variable of `Quot.ind`. -/
def qiFrTyB : Expr :=
  .forallE (Name.anonymous.str "a")
    (.app (.app (.const (Name.anonymous.str "Quot")
      [.param (Name.anonymous.str "u")]) qFrA) qFrR)
    (.sort .zero) ⟨.default, some (.succ .zero)⟩

def qiFrB : Expr := .fvar 2 (Name.anonymous.str "β") qiFrTyB

/-- The minor-premise annotation of `Quot.ind`. -/
def qiFrTyMk : Expr :=
  .forallE (Name.anonymous.str "a") qFrA
    (.app qiFrB (.app (.app (.app qFrMkC qFrA) qFrR) (.bvar 0)))
    ⟨.default, some .zero⟩

def qiFrMk : Expr := .fvar 3 (Name.anonymous.str "mk") qiFrTyMk

/-- The field frame variable of `Quot.ind`. -/
def qiFra : Expr := .fvar 4 (Name.anonymous.str "a") qFrA

/-- The `Quot.ind` head. -/
def qiFrRec : Expr :=
  .const ((Name.anonymous.str "Quot").str "ind")
    [.param (Name.anonymous.str "u")]

/-! ## Value-level folds at the constructor point -/

/-- `Quot.lift`'s value applied through its telescope at a class point
computes to the function's value. -/
theorem quotLiftVal_fold {Av Rv Bv fv hv av : V}
    (hA : Av ∈ˢ univ (ψ uN)) (hR : Rv ∈ˢ relSpace V (ψ uN) Av)
    (hB : Bv ∈ˢ univ (ψ vN)) (hf : fv ∈ˢ pi (ψ vN) Av fun _ => Bv)
    (hh : hv ∈ˢ quotInvSpace V Av Rv fv) (hav : av ∈ˢ Av) :
    SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
      (SetTheory.app (SetTheory.app (quotLiftVal V ψ) Av) Rv) Bv) fv) hv)
      (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) Av) Rv)
        av) = SetTheory.app fv av := by
  by_cases h0 : ψ vN = 0
  · have hVpt : (quotLiftVal V ψ : V) = pt := by
      simp only [quotLiftVal]
      refine lamC_of_forall fun A hA' => ?_
      refine lamC_of_forall fun R hR' => ?_
      refine lamC_of_forall fun B hB' => ?_
      refine lamC_of_forall fun f hf' => ?_
      refine lamC_of_forall fun h hh' => ?_
      refine lamC_of_forall fun q hq' => ?_
      rw [quotLift_app hq']
      exact mem_univ_zero (h0 ▸ hB')
        (app_mem_piC hf' (qrep_spec hq').1)
    rw [hVpt]
    simp only [app_pt]
    have hB0 : Bv ∈ˢ univ 0 := h0 ▸ hB
    exact (mem_univ_zero hB0 (app_mem hf hav (fun _ _ => hB))).symm
  · have hCL : ∀ A R', A ∈ˢ univ (ψ uN) → R' ∈ˢ relSpace V (ψ uN) A →
        quotSet (ψ uN) A R' ∈ˢ univ (ψ uN) :=
      fun A R' hA' _ => quotSet_mem_univ hA'
    have hGL : QlG V (ψ uN) (ψ vN) (fun A R' => quotSet (ψ uN) A R')
        (fun A R' f q =>
          SetTheory.app (quotLift (ψ uN) (ψ vN) A R' f) q) := by
      intro A R' B f h q hA' hR' hB' hf' hh' hq'
      exact app_mem (quotLift_mem hA' hf' (inv_of_invSpace' hA' hR' hh'))
        hq' (fun _ _ => hB')
    have hinv := inv_of_invSpace' hA hR hh
    rw [quotLiftVal_eq_qlVal h0, qlVal_app1 h0 hGL hCL hA,
      qlL1_app h0 hGL hCL hA hR, qlL2_app h0 hGL hCL hA hR hB,
      qlL3_app h0 hGL hCL hA hR hB hf,
      qlL4_app h0 hGL hCL hA hR hB hf hh,
      quotMkVal_app₃' hA hR hav,
      qlL5_app (quotClass_mem hav)
        (fun q hq => app_mem (quotLift_mem hA hf hinv) hq
          (fun _ _ => hB)) hB]
    exact quotLift_beta hA hav hinv

/-! ## Tower fibre facts for `Quot.lift`'s interpreted type -/

private theorem qlT5_univ {A R B : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) (hB : B ∈ˢ univ (ψ vN)) :
    (pi (ψ vN) (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
      fun _ => B) ∈ˢ univ (qlQ (ψ uN) (ψ vN)) := by
  rw [quotVal_app₂' hA hR]
  exact pi_mem_univ (u := ψ uN) (v := ψ vN) (quotSet_mem_univ hA)
    (fun _ _ => hB)

private theorem qlT4_univ {A R B f : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) (hB : B ∈ˢ univ (ψ vN))
    (hf : f ∈ˢ pi (ψ vN) A fun _ => B) :
    (pi (qlQ (ψ uN) (ψ vN)) (qlInvI V ψ A R B f)
      fun _ => pi (ψ vN) (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
        fun _ => B) ∈ˢ univ (qlV (ψ uN) (ψ vN)) := by
  have h := pi_mem_univ (u := 0) (v := qlQ (ψ uN) (ψ vN))
    (qlInvI_univ hA hR hB hf) (fun _ _ => qlT5_univ hA hR hB)
  have hcast : (if qlQ (ψ uN) (ψ vN) = 0 then 0
      else Nat.max 0 (qlQ (ψ uN) (ψ vN))) = qlV (ψ uN) (ψ vN) := by
    unfold qlV
    by_cases hq : qlQ (ψ uN) (ψ vN) = 0
    · simp [hq]
    · rw [if_neg hq, if_neg hq]
      exact Nat.zero_max _
  rw [hcast] at h
  exact h

private theorem qlT3_univ {A R B : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) (hB : B ∈ˢ univ (ψ vN)) :
    (pi (qlV (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B)
      fun f => pi (qlQ (ψ uN) (ψ vN)) (qlInvI V ψ A R B f)
        fun _ => pi (ψ vN)
          (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
          fun _ => B) ∈ˢ univ (qlB (ψ uN) (ψ vN)) := by
  have hdom : (pi (ψ vN) A fun _ => B) ∈ˢ univ (qlQ (ψ uN) (ψ vN)) :=
    pi_mem_univ (u := ψ uN) (v := ψ vN) hA (fun _ _ => hB)
  exact pi_mem_univ (u := qlQ (ψ uN) (ψ vN)) (v := qlV (ψ uN) (ψ vN))
    hdom (fun f hf => qlT4_univ hA hR hB hf)

private theorem qlT2_univ {A R : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) :
    (pi (qlB (ψ uN) (ψ vN)) (univ (ψ vN))
      fun B => pi (qlV (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B)
        fun f => pi (qlQ (ψ uN) (ψ vN)) (qlInvI V ψ A R B f)
          fun _ => pi (ψ vN)
            (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
            fun _ => B) ∈ˢ univ (qlR (ψ uN) (ψ vN)) :=
  pi_mem_univ (u := ψ vN + 1) (v := qlB (ψ uN) (ψ vN))
    (univ_mem_univ (ψ vN)) (fun _B hB => qlT3_univ hA hR hB)

private theorem qlT1_univ {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    (pi (qlR (ψ uN) (ψ vN)) (relSpace V (ψ uN) A)
      fun R => pi (qlB (ψ uN) (ψ vN)) (univ (ψ vN))
        fun B => pi (qlV (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B)
          fun f => pi (qlQ (ψ uN) (ψ vN)) (qlInvI V ψ A R B f)
            fun _ => pi (ψ vN)
              (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
              fun _ => B) ∈ˢ univ (qlA (ψ uN) (ψ vN)) := by
  have h := pi_mem_univ (u := Nat.max (ψ uN) 1) (v := qlR (ψ uN) (ψ vN))
    (relSpace_mem' hA) (fun R hR => qlT2_univ hA hR)
  have hcast : (if qlR (ψ uN) (ψ vN) = 0 then 0
      else Nat.max (Nat.max (ψ uN) 1) (qlR (ψ uN) (ψ vN))) =
      qlA (ψ uN) (ψ vN) := by
    unfold qlA
    rw [if_neg (max_ne_zero_r' (by decide) : Nat.max (ψ uN) 1 ≠ 0),
      max_absorb_l']
  rw [hcast] at h
  exact h

/-! ## Tower fibre facts for `Quot.ind`'s interpreted type (all
propositional) -/

private theorem qi_pi0_univ0 {u' : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ univ u') (hB : ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) :
    pi 0 A B ∈ˢ (univ 0 : V) := by
  have := pi_mem_univ (u := u') (v := 0) hA hB
  simpa using this

private theorem qi_minor_univ0 {A R B : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A)
    (hB : B ∈ˢ pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
      fun _ => univ 0) :
    (pi 0 A fun a => SetTheory.app B
      (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R)
        a)) ∈ˢ (univ 0 : V) := by
  refine qi_pi0_univ0 hA fun a ha => ?_
  refine app_mem hB ?_ (fun _ _ => univ_mem_univ 0)
  rw [quotVal_app₂' hA hR, quotMkVal_app₃' hA hR ha]
  exact quotClass_mem ha

private theorem qiT4_univ {A R B : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A)
    (hB : B ∈ˢ pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
      fun _ => univ 0) :
    (pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
      fun q => SetTheory.app B q) ∈ˢ (univ 0 : V) := by
  refine qi_pi0_univ0 (u' := ψ uN)
    (A := SetTheory.app (SetTheory.app (quotVal V ψ) A) R) ?_
    (fun q hq => app_mem hB hq (fun _ _ => univ_mem_univ 0))
  rw [quotVal_app₂' hA hR]
  exact quotSet_mem_univ hA

private theorem qiT3_univ {A R B : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A)
    (hB : B ∈ˢ pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
      fun _ => univ 0) :
    (pi 0 (pi 0 A fun a => SetTheory.app B
        (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R)
          a))
      fun _ => pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
        fun q => SetTheory.app B q) ∈ˢ (univ 0 : V) :=
  qi_pi0_univ0 (qi_minor_univ0 hA hR hB) (fun _ _ => qiT4_univ hA hR hB)

private theorem qiT2_univ {A R : V} (hA : A ∈ˢ univ (ψ uN))
    (hR : R ∈ˢ relSpace V (ψ uN) A) :
    (pi 0 (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
        fun _ => univ 0)
      fun B => pi 0 (pi 0 A fun a => SetTheory.app B
          (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A)
            R) a))
        fun _ => pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
          fun q => SetTheory.app B q) ∈ˢ (univ 0 : V) := by
  have hdom : (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
      fun _ => univ 0) ∈ˢ univ (Nat.max (ψ uN) 1) := by
    have := pi_mem_univ (u := ψ uN) (v := 1)
      (A := SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
      (B := fun _ => univ 0)
      (by rw [quotVal_app₂' hA hR]; exact quotSet_mem_univ hA)
      (fun _ _ => univ_mem_univ 0)
    simpa using this
  exact qi_pi0_univ0 hdom (fun B hB => qiT3_univ hA hR hB)

private theorem qiT1_univ {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    (pi 0 (relSpace V (ψ uN) A)
      fun R => pi 0 (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
          fun _ => univ 0)
        fun B => pi 0 (pi 0 A fun a => SetTheory.app B
            (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A)
              R) a))
          fun _ => pi 0 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
            fun q => SetTheory.app B q) ∈ˢ (univ 0 : V) :=
  qi_pi0_univ0 (relSpace_mem' hA) (fun _R hR => qiT2_univ hA hR)

/-! ## Stage facts for the two canonical frames -/

theorem qFr_interp_tyR {cval : ConstVal V} {A : V} :
    interpExpr V cval env ψ 1 (updV V (rho0 V) 0 A) qFrTyR =
      some (relSpace V (ψ uN) A) := by
  simp [qFrTyR, qFrA, relSpace, interpExpr, Expr.instantiate1, updV,
    Level.eval, uN]
  try rfl

theorem qFr_annotOk_tyR {cval : ConstVal V} {A : V}
    (hA : A ∈ˢ univ (ψ uN)) :
    AnnotOk V cval env ψ 1 (updV V (rho0 V) 0 A) qFrTyR := by
  simp only [qFrTyR, qFrA, AnnotOk]
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
  intro x Sx hSx hx
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
    intro y Sy hSy hy
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
    refine ⟨univ 0, ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
    · exact univ_mem_univ 0
  · refine ⟨pi 1 A (fun _ => univ 0), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
    · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
        hA (fun _ _ => univ_mem_univ 0)

theorem qlFr_interp_tyF {cval : ConstVal V} {A R B : V} :
    interpExpr V cval env ψ 3
      (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B) qlFrTyF =
      some (pi (ψ vN) A fun _ => B) := by
  simp [qlFrTyF, qFrA, qlFrB, interpExpr, Expr.instantiate1, updV,
    Level.eval, vN]
  try rfl

theorem qlFr_annotOk_tyF {cval : ConstVal V} {A R B : V}
    (hB : B ∈ˢ univ (ψ vN)) :
    AnnotOk V cval env ψ 3
      (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B) qlFrTyF := by
  simp only [qlFrTyF, qFrA, qlFrB, AnnotOk]
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
  intro x Sx hSx hx
  refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
  refine ⟨B, ?_, ?_⟩
  · simp [interpExpr, Expr.instantiate1, updV]
  · exact hB

theorem qlFr_interp_tyH {cval : ConstVal V} {A R B f : V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ') :
    interpExpr V cval env ψ 4
      (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B) 3 f)
      qlFrTyH = some (qlInvI V ψ A R B f) := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  simp [qlFrTyH, qFrA, qFrR, qFrTyR, qlFrB, qlFrF, qlFrTyF, qlInvI,
    interpExpr, Expr.instantiate1, updV, hfindE', hvalE', eqA,
    ConstantInfo.toConstantVal, Level.eval, Level.substFn,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

theorem qlFr_annotOk_tyH {cval : ConstVal V} {A R B f : V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hA : A ∈ˢ univ (ψ uN)) (hR : R ∈ˢ relSpace V (ψ uN) A)
    (hB : B ∈ˢ univ (ψ vN)) (hf : f ∈ˢ pi (ψ vN) A fun _ => B) :
    AnnotOk V cval env ψ 4
      (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B) 3 f)
      qlFrTyH := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfa : ∀ x, x ∈ˢ A → SetTheory.app f x ∈ˢ B :=
    fun x hx => app_mem hf hx (fun _ _ => hB)
  have heqbody : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A →
      SetTheory.app (SetTheory.app (SetTheory.app
        (eqVal V (Level.substFn ψ [uN] [Level.param vN])) B)
        (SetTheory.app f a')) (SetTheory.app f b') ∈ˢ univ 0 := by
    intro a' b' ha' hb'
    rw [eqVal_app₃ (ψ := Level.substFn ψ [uN] [Level.param vN]) hB
      (hfa a' ha') (hfa b' hb')]
    exact eqv_mem_univ _ _
  simp only [qlFrTyH, qFrA, qFrR, qFrTyR, qlFrB, qlFrF, qlFrTyF, AnnotOk]
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
  intro a' Sa hSa ha'
  have hSa' : Sa = A := by
    simp [interpExpr, updV] at hSa
    exact hSa.symm
  rw [hSa'] at ha'
  refine ⟨?_, ?_⟩
  · -- opened `∀ (b : α), r a b → Eq β (f a) (f b)`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), 0, ?_⟩
    refine ⟨?_, ?_⟩
    · first
        | (rintro v ⟨rfl⟩; exact fun z hz => hz)
        | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
        | (rintro v ⟨rfl⟩
           intro z hz
           refine univ_mono ?_ z hz
           simp only [Level.eval, qtA, qmR, qmA, qlQ, qlV, qlB, qlR, qlA, qlψ, uN, vN]
           by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2] <;> omega)
    intro b' Sb hSb hb'
    have hSb' : Sb = A := by
      simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
        Option.some.injEq] at hSb
      exact hSb.symm
    rw [hSb'] at hb'
    refine ⟨?_, ?_⟩
    · -- opened `r a b → Eq β (f a) (f b)`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨?_, 0, ?_⟩
      · -- AnnotOk of `r a b`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
            (by simp [Expr.instantiate1, AnnotOk]),
            R, a', Nat.max (ψ uN) 1, A,
            (fun _ => pi 1 A fun _ => univ 0),
            (by simp [interpExpr, Expr.instantiate1, updV]),
            (by simp [interpExpr, Expr.instantiate1, updV]),
            hR, ha', fun x _ =>
              pi_mem_univ (u := ψ uN) (v := 1)
                (B := fun _ => univ 0) hA
                (fun _ _ => univ_mem_univ 0)⟩,
          (by simp [Expr.instantiate1, AnnotOk]),
          SetTheory.app R a', b', 1, A, (fun _ => univ 0),
          (by simp [interpExpr, Expr.instantiate1, updV]),
          (by simp [interpExpr, Expr.instantiate1, updV]),
          ?_, hb', fun _ _ => univ_mem_univ 0⟩
        exact app_mem hR ha' (fun x _ =>
          pi_mem_univ (u := ψ uN) (v := 1)
            (B := fun _ => univ 0) hA
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
        intro w Sw _hSw _hw
        refine ⟨?_, ?_⟩
        · -- AnnotOk of `Eq β (f a) (f b)`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
              (by simp [Expr.instantiate1, AnnotOk]),
              eqVal V (Level.substFn ψ [uN] [Level.param vN]),
              B, Nat.max (ψ vN) (Nat.max (ψ vN) 1),
              univ (ψ vN),
              (fun X => pi (Nat.max (ψ vN) 1) X fun _ =>
                pi 1 X fun _ => univ 0),
              ?_, ?_,
              eqVal_mem (ψ := Level.substFn ψ [uN] [Level.param vN]),
              hB,
              fun X hX => eq_fibre_mem
                (ψ := Level.substFn ψ [uN] [Level.param vN]) hX⟩,
            ⟨(by simp [Expr.instantiate1, AnnotOk]),
              (by simp [Expr.instantiate1, AnnotOk]),
              f, a', ψ vN, A, (fun _ => B),
              (by simp [interpExpr, Expr.instantiate1, updV]),
              (by simp [interpExpr, Expr.instantiate1, updV]),
              hf, ha', fun _ _ => hB⟩,
            SetTheory.app (eqVal V (Level.substFn ψ [uN]
              [Level.param vN])) B,
            SetTheory.app f a', Nat.max (ψ vN) 1, B,
            (fun _ => pi 1 B fun _ => univ 0),
            ?_, ?_,
            eqVal_app_mem (ψ := Level.substFn ψ [uN]
              [Level.param vN]) hB,
            hfa a' ha', fun y _ =>
              pi_mem_univ (u := ψ vN) (v := 1)
                (B := fun _ => univ 0) hB
                (fun _ _ => univ_mem_univ 0)⟩,
            ⟨(by simp [Expr.instantiate1, AnnotOk]),
              (by simp [Expr.instantiate1, AnnotOk]),
              f, b', ψ vN, A, (fun _ => B),
              (by simp [interpExpr, Expr.instantiate1, updV]),
              (by simp [interpExpr, Expr.instantiate1, updV]),
              hf, hb', fun _ _ => hB⟩,
            SetTheory.app (SetTheory.app (eqVal V
              (Level.substFn ψ [uN] [Level.param vN]))
              B) (SetTheory.app f a'),
            SetTheory.app f b', 1, B, (fun _ => univ 0),
            ?_, ?_,
            eqVal_app₂_mem (ψ := Level.substFn ψ [uN]
              [Level.param vN]) hB (hfa a' ha'),
            hfa b' hb', fun _ _ => univ_mem_univ 0⟩
          · simp [interpExpr, Expr.instantiate1, updV, uN, vN, hfindE',
              hvalE', eqA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
          · simp [interpExpr, Expr.instantiate1, updV, uN, vN, hfindE',
              hvalE', eqA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
          · simp [interpExpr, Expr.instantiate1, updV, uN, vN, hfindE',
              hvalE', eqA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
        · -- fibre of the `r a b` binder (cod `0`)
          refine ⟨SetTheory.app (SetTheory.app (SetTheory.app
            (eqVal V (Level.substFn ψ [uN] [Level.param vN])) B)
            (SetTheory.app f a')) (SetTheory.app f b'), ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, uN, vN, hfindE',
              hvalE', eqA, ConstantInfo.toConstantVal]
            try rfl
          · exact heqbody a' b' ha' hb'
    · -- fibre of the `b` binder (cod `imax 0 0`)
      refine ⟨pi 0 (SetTheory.app (SetTheory.app R a') b')
        fun _ => SetTheory.app (SetTheory.app (SetTheory.app
          (eqVal V (Level.substFn ψ [uN] [Level.param vN])) B)
          (SetTheory.app f a')) (SetTheory.app f b'), ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, uN, vN, hfindE',
          hvalE', eqA, ConstantInfo.toConstantVal]
        try rfl
      · refine pi_mem_univ (u := 0) (v := 0)
          (rel_app₂_univ' hA hR ha' hb')
          (fun x _ => heqbody a' b' ha' hb')
  · -- fibre of the `a` binder (cod `imax u (imax 0 0)`)
    refine ⟨pi 0 A (fun b' => pi 0 (SetTheory.app (SetTheory.app R a') b')
      fun _ => SetTheory.app (SetTheory.app (SetTheory.app
        (eqVal V (Level.substFn ψ [uN] [Level.param vN])) B)
        (SetTheory.app f a')) (SetTheory.app f b')), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, uN, vN, hfindE',
        hvalE', eqA, ConstantInfo.toConstantVal]
      try rfl
    · exact qi_pi0_univ0 (u' := ψ uN) hA
        (fun b' hb' => qi_pi0_univ0 (rel_app₂_univ' hA hR ha' hb')
          (fun _ _ => heqbody a' b' ha' hb'))

theorem qiFr_interp_tyB {cval : ConstVal V} {A R : V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ') :
    interpExpr V cval env ψ 2 (updV V (updV V (rho0 V) 0 A) 1 R)
      qiFrTyB =
      some (pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
        fun _ => univ 0) := by
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA :=
    hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  simp [qiFrTyB, qFrA, qFrR, qFrTyR, interpExpr, Expr.instantiate1, updV,
    hfindQ', hvalQ', quotA, ConstantInfo.toConstantVal, Level.eval,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

theorem qiFr_annotOk_tyB {cval : ConstVal V} {A R : V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hA : A ∈ˢ univ (ψ uN)) (hR : R ∈ˢ relSpace V (ψ uN) A) :
    AnnotOk V cval env ψ 2 (updV V (updV V (rho0 V) 0 A) 1 R) qiFrTyB := by
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA :=
    hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  simp only [qiFrTyB, qFrA, qFrR, qFrTyR, AnnotOk]
  refine ⟨⟨⟨trivial, trivial,
      quotVal V ψ, A, ψ uN + 1, univ (ψ uN),
      (fun X => pi (ψ uN + 1) (relSpace V (ψ uN) X) fun _ =>
        univ (ψ uN)),
      ?_, ?_, quotVal_mem', hA, fun X hX => quotVal_fib_univ' hX⟩,
    trivial,
    SetTheory.app (quotVal V ψ) A, R, ψ uN + 1, relSpace V (ψ uN) A,
      (fun _ => univ (ψ uN)),
      ?_, ?_, quotVal_app_mem' hA, hR,
      fun _ _ => univ_mem_univ (ψ uN)⟩, 1, ?_⟩
  · simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ', quotA,
      ConstantInfo.toConstantVal]
    try rfl
  · simp [interpExpr, Expr.instantiate1, updV]
  · rw [interpExpr]
    simp [interpExpr, Expr.instantiate1, updV, hfindQ', hvalQ', quotA,
      ConstantInfo.toConstantVal]
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
    intro q Sq hSq hq
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
    refine ⟨univ 0, ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
    · exact univ_mem_univ 0

theorem qiFr_interp_tyMk {cval : ConstVal V} {A R B : V}
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ') :
    interpExpr V cval env ψ 3
      (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B) qiFrTyMk =
      some (pi 0 A fun a => SetTheory.app B
        (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R)
          a)) := by
  have hfindMk' : env.find? ((Name.anonymous.str "Quot").str "mk") =
      some quotMkA := hfindMk
  have hvalMk' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "mk") ψ' = quotMkVal V ψ' :=
    hvalMk
  simp [qiFrTyMk, qiFrB, qiFrTyB, qFrMkC, qFrA, qFrR, qFrTyR, interpExpr,
    Expr.instantiate1, updV, hfindMk', hvalMk', quotMkA,
    ConstantInfo.toConstantVal, Level.eval,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

theorem qiFr_annotOk_tyMk {cval : ConstVal V} {A R B : V}
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ')
    (hA : A ∈ˢ univ (ψ uN)) (hR : R ∈ˢ relSpace V (ψ uN) A)
    (hB : B ∈ˢ pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ) A) R)
      fun _ => univ 0) :
    AnnotOk V cval env ψ 3
      (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B) qiFrTyMk := by
  have hfindMk' : env.find? ((Name.anonymous.str "Quot").str "mk") =
      some quotMkA := hfindMk
  have hvalMk' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "mk") ψ' = quotMkVal V ψ' :=
    hvalMk
  have hchain : ∀ a, a ∈ˢ A →
      SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R)
        a ∈ˢ SetTheory.app (SetTheory.app (quotVal V ψ) A) R := by
    intro a ha
    rw [quotVal_app₂' hA hR, quotMkVal_app₃' hA hR ha]
    exact quotClass_mem ha
  simp only [qiFrTyMk, qiFrB, qiFrTyB, qFrMkC, qFrA, qFrR, qFrTyR, AnnotOk]
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
  intro a Sa hSa ha
  have hSa' : Sa = A := by
    simp [interpExpr, updV] at hSa
    exact hSa.symm
  rw [hSa'] at ha
  refine ⟨?_, ?_⟩
  · -- the body `β (Quot.mk α r a)`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
      ⟨⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
        (by simp [Expr.instantiate1, AnnotOk]),
        quotMkVal V ψ, A, ψ uN, univ (ψ uN),
        (fun X => pi (ψ uN) (relSpace V (ψ uN) X) fun R' =>
          pi (ψ uN) X fun _ => quotSet (ψ uN) X R'),
        ?_, ?_, quotMkVal_mem', hA, fun X hX => quotMkD1_univ' hX⟩,
      (by simp [Expr.instantiate1, AnnotOk]),
      SetTheory.app (quotMkVal V ψ) A, R, ψ uN, relSpace V (ψ uN) A,
        (fun R' => pi (ψ uN) A fun _ => quotSet (ψ uN) A R'),
        ?_, ?_, quotMkVal_app_mem' hA, hR,
        fun R' _ => quotMkD2_univ' hA⟩,
      (by simp [Expr.instantiate1, AnnotOk]),
      SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R, a, ψ uN, A,
        (fun _ => quotSet (ψ uN) A R),
        ?_, ?_, quotMkVal_app₂_mem' hA hR, ha,
        fun _ _ => quotSet_mem_univ hA⟩,
      B,
      SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ) A) R)
        a,
      1, SetTheory.app (SetTheory.app (quotVal V ψ) A) R,
      (fun _ => univ 0),
      ?_, ?_, hB, hchain a ha, fun _ _ => univ_mem_univ 0⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindMk', hvalMk',
        quotMkA, ConstantInfo.toConstantVal]
      try rfl
    · simp [interpExpr, Expr.instantiate1, updV]
    · rw [interpExpr]
      simp [interpExpr, Expr.instantiate1, updV, hfindMk', hvalMk',
        quotMkA, ConstantInfo.toConstantVal]
      try rfl
    · simp [interpExpr, Expr.instantiate1, updV]
    · rw [interpExpr]
      rw [interpExpr]
      simp [interpExpr, Expr.instantiate1, updV, hfindMk', hvalMk',
        quotMkA, ConstantInfo.toConstantVal]
      try rfl
    · simp [interpExpr, Expr.instantiate1, updV]
    · simp [interpExpr, Expr.instantiate1, updV]
    · rw [interpExpr]
      rw [interpExpr]
      rw [interpExpr]
      simp [interpExpr, Expr.instantiate1, updV, hfindMk', hvalMk',
        quotMkA, ConstantInfo.toConstantVal]
      try rfl
  · refine ⟨SetTheory.app B (SetTheory.app (SetTheory.app
      (SetTheory.app (quotMkVal V ψ) A) R) a), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindMk', hvalMk',
        quotMkA, ConstantInfo.toConstantVal]
      try rfl
    · exact app_mem hB (hchain a ha) (fun _ _ => univ_mem_univ 0)

/-! ## The `RecRulesOk` clauses of the two eliminators -/

/-- The `RecRulesOk` clause of `Quot.lift`'s synthetic rule. -/
theorem quotLift_ruleOk {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ')
    (hfindL : env.find? quotLiftName = some quotLiftA)
    (hvalL : ∀ ψ' : Name → Nat,
      cval quotLiftName ψ' = quotLiftVal V ψ') :
    ∃ fvms bL,
      ruleLhsParts quotLiftName quotLiftA.toConstantVal 5
        ((ConstantInfo.recRules quotLiftA).getD 0 default)
        quotMkA.toConstantVal = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = 5 +
        RecRule.nfields ((ConstantInfo.recRules quotLiftA).getD 0 default) ∧
      (closeLamsAt fvms bL).constsResolve env = true ∧
      ∀ ψ' : Name → Nat,
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' quotLiftRhsA = some Rv := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA :=
    hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  have hfindMk' : env.find? ((Name.anonymous.str "Quot").str "mk") =
      some quotMkA := hfindMk
  have hvalMk' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "mk") ψ' = quotMkVal V ψ' :=
    hvalMk
  have hfindL' : env.find? ((Name.anonymous.str "Quot").str "lift") =
      some quotLiftA := hfindL
  have hvalL' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "lift") ψ' =
        quotLiftVal V ψ' := hvalL
  have hparts : ruleLhsParts quotLiftName quotLiftA.toConstantVal 5
      ((ConstantInfo.recRules quotLiftA).getD 0 default)
      quotMkA.toConstantVal = some
      ([(qFrA, ⟨.default, some (.imax
          (.imax (.param (Name.anonymous.str "u"))
            (.imax (.param (Name.anonymous.str "u")) (.succ .zero)))
          (.imax (.succ (.param (Name.anonymous.str "v")))
            (.imax (.imax (.param (Name.anonymous.str "u"))
              (.param (Name.anonymous.str "v")))
              (.imax (.imax (.param (Name.anonymous.str "u"))
                (.imax (.param (Name.anonymous.str "u"))
                  (.imax .zero .zero)))
                (.imax (.param (Name.anonymous.str "u"))
                  (.param (Name.anonymous.str "v")))))))⟩),
        (qFrR, ⟨.default, some (.imax
          (.succ (.param (Name.anonymous.str "v")))
          (.imax (.imax (.param (Name.anonymous.str "u"))
            (.param (Name.anonymous.str "v")))
            (.imax (.imax (.param (Name.anonymous.str "u"))
              (.imax (.param (Name.anonymous.str "u"))
                (.imax .zero .zero)))
              (.imax (.param (Name.anonymous.str "u"))
                (.param (Name.anonymous.str "v"))))))⟩),
        (qlFrB, ⟨.default, some (.imax
          (.imax (.param (Name.anonymous.str "u"))
            (.param (Name.anonymous.str "v")))
          (.imax (.imax (.param (Name.anonymous.str "u"))
            (.imax (.param (Name.anonymous.str "u"))
              (.imax .zero .zero)))
            (.imax (.param (Name.anonymous.str "u"))
              (.param (Name.anonymous.str "v")))))⟩),
        (qlFrF, ⟨.default, some (.imax
          (.imax (.param (Name.anonymous.str "u"))
            (.imax (.param (Name.anonymous.str "u")) (.imax .zero .zero)))
          (.imax (.param (Name.anonymous.str "u"))
            (.param (Name.anonymous.str "v"))))⟩),
        (qlFrH, ⟨.default, some (.imax (.param (Name.anonymous.str "u"))
          (.param (Name.anonymous.str "v")))⟩),
        (qlFrq, ⟨.default, some (.param (Name.anonymous.str "v"))⟩)],
       .app (.app (.app (.app (.app (.app qlFrRec qFrA) qFrR) qlFrB)
           qlFrF) qlFrH)
         (.app (.app (.app qFrMkC qFrA) qFrR) qlFrq)) := by rfl
  obtain ⟨hwf, hlen⟩ := ruleLhsParts_frameWf hparts rfl rfl rfl rfl
    (fun _ _ h => nomatch h)
  refine ⟨_, _, hparts, hwf, hlen, ?_, ?_⟩
  · exact ruleLhsParts_resolve hparts
      (by rw [hfindL]; rfl)
      (show (env.find? ((Name.anonymous.str "Quot").str "mk")).isSome =
          true by rw [hfindMk']; rfl)
      (by simp [ConstantInfo.toConstantVal, quotLiftA, Expr.constsResolve,
        hfindE', hfindQ'])
      (by simp [ConstantInfo.toConstantVal, quotMkA, Expr.constsResolve,
        hfindQ'])
      (fun _ _ h => nomatch h)
  · intro ψ'
    have hAR : AnnotOk V cval env ψ' 0 (rho0 V) quotLiftRhsA :=
      annotOk_quotLift_rhs (cval := cval) (ψ := ψ') hfindE hvalE
    have hstep : ∀ {fvms : List (Expr × BinderMeta)} {bL : Expr},
        FrameWf 0 fvms bL →
        TowerOk (V := V) cval env ψ' 0 (rho0 V) fvms bL quotLiftRhsA →
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' quotLiftRhsA = some Rv := by
      intro fvms bL hwf' ht
      obtain ⟨⟨Rv, hL, hR⟩, hA⟩ := TowerOk.out ht hwf' hAR
      exact ⟨hA, Rv, hL, hR⟩
    refine hstep hwf ?_
    have hityA : interpExpr V cval env ψ' 0 (rho0 V)
        (Expr.sort (Level.param (Name.anonymous.str "u"))) =
        some (univ (ψ' uN)) := by
      simp [interpExpr, Level.eval, uN]
    refine TowerOk.cons (A := univ (ψ' uN)) hityA hityA
      (by simp [AnnotOk]) ?_
    intro A hA
    refine TowerOk.cons (A := relSpace V (ψ' uN) A)
      (qFr_interp_tyR (cval := cval)) (qFr_interp_tyR (cval := cval))
      (qFr_annotOk_tyR hA) ?_
    intro R hR
    have hityB : interpExpr V cval env ψ' 2
        (updV V (updV V (rho0 V) 0 A) 1 R)
        (Expr.sort (Level.param (Name.anonymous.str "v"))) =
        some (univ (ψ' vN)) := by
      simp [interpExpr, Level.eval, vN]
    refine TowerOk.cons (A := univ (ψ' vN)) hityB hityB
      (by simp [AnnotOk]) ?_
    intro B hB
    refine TowerOk.cons (A := pi (ψ' vN) A fun _ => B)
      (qlFr_interp_tyF (cval := cval)) (qlFr_interp_tyF (cval := cval))
      (qlFr_annotOk_tyF hB) ?_
    intro f hf
    refine TowerOk.cons (A := qlInvI V ψ' A R B f)
      (qlFr_interp_tyH hfindE hvalE) (qlFr_interp_tyH hfindE hvalE)
      (qlFr_annotOk_tyH hfindE hvalE hA hR hB hf) ?_
    intro h hh
    have hityq : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 f) 4 h) qFrA = some A := by
      simp [qFrA, interpExpr, updV]
    refine TowerOk.cons (A := A) hityq hityq
      (by simp [qFrA, AnnotOk]) ?_
    intro a ha
    have hh' : h ∈ˢ quotInvSpace V A R f := qlInvEq hB hf ▸ hh
    have hsub2 : Level.substFn ψ'
        [Name.anonymous.str "u", Name.anonymous.str "v"]
        [Level.param (Name.anonymous.str "u"),
         Level.param (Name.anonymous.str "v")] = ψ' :=
      funext fun _ => Level.substFn_map_param
    have hsub1 : Level.substFn ψ' [Name.anonymous.str "u"]
        [Level.param (Name.anonymous.str "u")] = ψ' :=
      funext fun _ => Level.substFn_map_param
    have hirec : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) qlFrRec = some (quotLiftVal V ψ') := by
      simp only [qlFrRec, interpExpr, hfindL', quotLiftA,
        ConstantInfo.toConstantVal, List.length_cons, List.length_nil,
        reduceIte, hsub2, hvalL']
    have himkC : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) qFrMkC = some (quotMkVal V ψ') := by
      simp only [qFrMkC, interpExpr, hfindMk', quotMkA,
        ConstantInfo.toConstantVal, List.length_cons, List.length_nil,
        reduceIte, hsub1, hvalMk']
    have hifvA : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) qFrA = some A := by
      simp [qFrA, interpExpr, updV]
    have hifvR : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) qFrR = some R := by
      simp [qFrR, interpExpr, updV]
    have hifvB : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) qlFrB = some B := by
      simp [qlFrB, interpExpr, updV]
    have hifvF : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) qlFrF = some f := by
      simp [qlFrF, interpExpr, updV]
    have hifvH : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) qlFrH = some h := by
      simp [qlFrH, interpExpr, updV]
    have hifvq : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) qlFrq = some a := by
      simp [qlFrq, interpExpr, updV]
    have hip1 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) (.app qlFrRec qFrA) =
        some (SetTheory.app (quotLiftVal V ψ') A) := by
      rw [interpExpr, hirec, hifvA]
    have hip2 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) (.app (.app qlFrRec qFrA) qFrR) =
        some (SetTheory.app (SetTheory.app (quotLiftVal V ψ') A) R) := by
      rw [interpExpr, hip1, hifvR]
    have hip3 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a)
        (.app (.app (.app qlFrRec qFrA) qFrR) qlFrB) =
        some (SetTheory.app (SetTheory.app (SetTheory.app
          (quotLiftVal V ψ') A) R) B) := by
      rw [interpExpr, hip2, hifvB]
    have hip4 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a)
        (.app (.app (.app (.app qlFrRec qFrA) qFrR) qlFrB) qlFrF) =
        some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (quotLiftVal V ψ') A) R) B) f) := by
      rw [interpExpr, hip3, hifvF]
    have hip5 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a)
        (.app (.app (.app (.app (.app qlFrRec qFrA) qFrR) qlFrB) qlFrF)
          qlFrH) =
        some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (quotLiftVal V ψ') A) R) B) f) h) := by
      rw [interpExpr, hip4, hifvH]
    have hiq1 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) (.app qFrMkC qFrA) =
        some (SetTheory.app (quotMkVal V ψ') A) := by
      rw [interpExpr, himkC, hifvA]
    have hiq2 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a) (.app (.app qFrMkC qFrA) qFrR) =
        some (SetTheory.app (SetTheory.app (quotMkVal V ψ') A) R) := by
      rw [interpExpr, hiq1, hifvR]
    have hiq3 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a)
        (.app (.app (.app qFrMkC qFrA) qFrR) qlFrq) =
        some (SetTheory.app (SetTheory.app (SetTheory.app
          (quotMkVal V ψ') A) R) a) := by
      rw [interpExpr, hiq2, hifvq]
    obtain ⟨T, hT, hmem⟩ := quotLift_key (cval := cval) (env := env)
      (ψ := ψ') hfindE hvalE hfindQ hvalQ
    rw [interp_quotLift_type hfindE hvalE hfindQ hvalQ] at hT
    obtain rfl := Option.some.inj hT
    have hm1 := app_mem hmem hA (fun A' hA' => qlT1_univ hA')
    have hm2 := app_mem hm1 hR (fun R' hR' => qlT2_univ hA hR')
    have hm3 := app_mem hm2 hB (fun B' hB' => qlT3_univ hA hR hB')
    have hm4 := app_mem hm3 hf (fun f' hf' => qlT4_univ hA hR hB hf')
    have hm5 := app_mem hm4 hh (fun _ _ => qlT5_univ hA hR hB)
    have hqv : SetTheory.app (SetTheory.app (SetTheory.app
        (quotMkVal V ψ') A) R) a ∈ˢ
        SetTheory.app (SetTheory.app (quotVal V ψ') A) R := by
      rw [quotVal_app₂' hA hR, quotMkVal_app₃' hA hR ha]
      exact quotClass_mem ha
    refine TowerOk.nil (w := SetTheory.app f a) ?_ ?_ ?_
    · rw [interpExpr, hip5, hiq3]
      show some (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (SetTheory.app (quotLiftVal V ψ') A)
          R) B) f) h)
        (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ') A)
          R) a)) = some (SetTheory.app f a)
      rw [quotLiftVal_fold hA hR hB hf hh' ha]
    · show interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R)
          2 B) 3 f) 4 h) 5 a)
        (.app qlFrF qlFrq) = some (SetTheory.app f a)
      rw [interpExpr, hifvF, hifvq]
    · simp only [AnnotOk, qlFrRec, qFrMkC, qFrA, qFrR, qFrTyR, qlFrB,
        qlFrF, qlFrTyF, qlFrH, qlFrTyH, qlFrq]
      exact ⟨⟨⟨⟨⟨⟨trivial, trivial,
          quotLiftVal V ψ', A, qlA (ψ' uN) (ψ' vN), univ (ψ' uN), _,
          hirec, hifvA, hmem, hA, fun A' hA' => qlT1_univ hA'⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
        SetTheory.app (quotLiftVal V ψ') A, R, qlR (ψ' uN) (ψ' vN),
          relSpace V (ψ' uN) A, _,
          hip1, hifvR, hm1, hR, fun R' hR' => qlT2_univ hA hR'⟩,
        trivial,
        SetTheory.app (SetTheory.app (quotLiftVal V ψ') A) R, B,
          qlB (ψ' uN) (ψ' vN), univ (ψ' vN), _,
          hip2, hifvB, hm2, hB, fun B' hB' => qlT3_univ hA hR hB'⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
        SetTheory.app (SetTheory.app (SetTheory.app (quotLiftVal V ψ') A)
          R) B, f, qlV (ψ' uN) (ψ' vN), pi (ψ' vN) A (fun _ => B), _,
          hip3, hifvF, hm3, hf, fun f' hf' => qlT4_univ hA hR hB hf'⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
        SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (quotLiftVal V ψ') A) R) B) f, h, qlQ (ψ' uN) (ψ' vN),
          qlInvI V ψ' A R B f, _,
          hip4, hifvH, hm4, hh, fun _ _ => qlT5_univ hA hR hB⟩,
        ⟨⟨⟨trivial, trivial,
          quotMkVal V ψ', A, ψ' uN, univ (ψ' uN),
          (fun X => pi (ψ' uN) (relSpace V (ψ' uN) X) fun R' =>
            pi (ψ' uN) X fun _ => quotSet (ψ' uN) X R'),
          himkC, hifvA, quotMkVal_mem', hA,
          fun X hX => quotMkD1_univ' hX⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
        SetTheory.app (quotMkVal V ψ') A, R, ψ' uN,
          relSpace V (ψ' uN) A,
          (fun R' => pi (ψ' uN) A fun _ => quotSet (ψ' uN) A R'),
          hiq1, hifvR, quotMkVal_app_mem' hA, hR,
          fun R' _ => quotMkD2_univ' hA⟩,
        trivial,
        SetTheory.app (SetTheory.app (quotMkVal V ψ') A) R, a, ψ' uN, A,
          (fun _ => quotSet (ψ' uN) A R),
          hiq2, hifvq, quotMkVal_app₂_mem' hA hR, ha,
          fun _ _ => quotSet_mem_univ hA⟩,
        SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (quotLiftVal V ψ') A) R) B) f) h,
        SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ') A)
          R) a,
        ψ' vN, SetTheory.app (SetTheory.app (quotVal V ψ') A) R,
        (fun _ => B),
        hip5, hiq3, hm5, hqv, fun _ _ => hB⟩

/-- The `RecRulesOk` clause of `Quot.ind`'s synthetic rule. -/
theorem quotInd_ruleOk {cval : ConstVal V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ')
    (hfindI : env.find? quotIndName = some quotIndA)
    (hvalI : ∀ ψ' : Name → Nat,
      cval quotIndName ψ' = quotIndVal V ψ') :
    ∃ fvms bL,
      ruleLhsParts quotIndName quotIndA.toConstantVal 4
        ((ConstantInfo.recRules quotIndA).getD 0 default)
        quotMkA.toConstantVal = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = 4 +
        RecRule.nfields ((ConstantInfo.recRules quotIndA).getD 0 default) ∧
      (closeLamsAt fvms bL).constsResolve env = true ∧
      ∀ ψ' : Name → Nat,
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' quotIndRhsA = some Rv := by
  have hfindQ' : env.find? (Name.anonymous.str "Quot") = some quotA :=
    hfindQ
  have hvalQ' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Quot") ψ' = quotVal V ψ' := hvalQ
  have hfindMk' : env.find? ((Name.anonymous.str "Quot").str "mk") =
      some quotMkA := hfindMk
  have hvalMk' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "mk") ψ' = quotMkVal V ψ' :=
    hvalMk
  have hfindI' : env.find? ((Name.anonymous.str "Quot").str "ind") =
      some quotIndA := hfindI
  have hvalI' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Quot").str "ind") ψ' = quotIndVal V ψ' :=
    hvalI
  have hparts : ruleLhsParts quotIndName quotIndA.toConstantVal 4
      ((ConstantInfo.recRules quotIndA).getD 0 default)
      quotMkA.toConstantVal = some
      ([(qFrA, ⟨.default, some (.imax
          (.imax (.param (Name.anonymous.str "u"))
            (.imax (.param (Name.anonymous.str "u")) (.succ .zero)))
          (.imax (.imax (.param (Name.anonymous.str "u")) (.succ .zero))
            (.imax (.imax (.param (Name.anonymous.str "u")) .zero)
              (.imax (.param (Name.anonymous.str "u")) .zero))))⟩),
        (qFrR, ⟨.default, some (.imax
          (.imax (.param (Name.anonymous.str "u")) (.succ .zero))
          (.imax (.imax (.param (Name.anonymous.str "u")) .zero)
            (.imax (.param (Name.anonymous.str "u")) .zero)))⟩),
        (qiFrB, ⟨.default, some (.imax
          (.imax (.param (Name.anonymous.str "u")) .zero)
          (.imax (.param (Name.anonymous.str "u")) .zero))⟩),
        (qiFrMk, ⟨.default,
          some (.imax (.param (Name.anonymous.str "u")) .zero)⟩),
        (qiFra, ⟨.default, some .zero⟩)],
       .app (.app (.app (.app (.app qiFrRec qFrA) qFrR) qiFrB) qiFrMk)
         (.app (.app (.app qFrMkC qFrA) qFrR) qiFra)) := by rfl
  obtain ⟨hwf, hlen⟩ := ruleLhsParts_frameWf hparts rfl rfl rfl rfl
    (fun _ _ h => nomatch h)
  refine ⟨_, _, hparts, hwf, hlen, ?_, ?_⟩
  · exact ruleLhsParts_resolve hparts
      (by rw [hfindI]; rfl)
      (show (env.find? ((Name.anonymous.str "Quot").str "mk")).isSome =
          true by rw [hfindMk']; rfl)
      (by simp [ConstantInfo.toConstantVal, quotIndA, Expr.constsResolve,
        hfindQ', hfindMk'])
      (by simp [ConstantInfo.toConstantVal, quotMkA, Expr.constsResolve,
        hfindQ'])
      (fun _ _ h => nomatch h)
  · intro ψ'
    have hAR : AnnotOk V cval env ψ' 0 (rho0 V) quotIndRhsA :=
      annotOk_quotInd_rhs (cval := cval) (ψ := ψ') hfindQ hvalQ hfindMk
        hvalMk
    have hstep : ∀ {fvms : List (Expr × BinderMeta)} {bL : Expr},
        FrameWf 0 fvms bL →
        TowerOk (V := V) cval env ψ' 0 (rho0 V) fvms bL quotIndRhsA →
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' quotIndRhsA = some Rv := by
      intro fvms bL hwf' ht
      obtain ⟨⟨Rv, hL, hR⟩, hA⟩ := TowerOk.out ht hwf' hAR
      exact ⟨hA, Rv, hL, hR⟩
    refine hstep hwf ?_
    have hityA : interpExpr V cval env ψ' 0 (rho0 V)
        (Expr.sort (Level.param (Name.anonymous.str "u"))) =
        some (univ (ψ' uN)) := by
      simp [interpExpr, Level.eval, uN]
    refine TowerOk.cons (A := univ (ψ' uN)) hityA hityA
      (by simp [AnnotOk]) ?_
    intro A hA
    refine TowerOk.cons (A := relSpace V (ψ' uN) A)
      (qFr_interp_tyR (cval := cval)) (qFr_interp_tyR (cval := cval))
      (qFr_annotOk_tyR hA) ?_
    intro R hR
    refine TowerOk.cons (A := pi 1
        (SetTheory.app (SetTheory.app (quotVal V ψ') A) R) fun _ => univ 0)
      (qiFr_interp_tyB hfindQ hvalQ) (qiFr_interp_tyB hfindQ hvalQ)
      (qiFr_annotOk_tyB hfindQ hvalQ hA hR) ?_
    intro B hB
    refine TowerOk.cons (A := pi 0 A fun a => SetTheory.app B
        (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ') A)
          R) a))
      (qiFr_interp_tyMk hfindMk hvalMk) (qiFr_interp_tyMk hfindMk hvalMk)
      (qiFr_annotOk_tyMk hfindMk hvalMk hA hR hB) ?_
    intro mk hmk
    have hitya : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B) 3 mk)
        qFrA = some A := by
      simp [qFrA, interpExpr, updV]
    refine TowerOk.cons (A := A) hitya hitya
      (by simp [qFrA, AnnotOk]) ?_
    intro a ha
    have hmkpt : mk = pt :=
      mem_univ_zero (qi_minor_univ0 hA hR hB) hmk
    have hsub1 : Level.substFn ψ' [Name.anonymous.str "u"]
        [Level.param (Name.anonymous.str "u")] = ψ' :=
      funext fun _ => Level.substFn_map_param
    have hirec : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) qiFrRec = some (quotIndVal V ψ') := by
      simp only [qiFrRec, interpExpr, hfindI', quotIndA,
        ConstantInfo.toConstantVal, List.length_cons, List.length_nil,
        reduceIte, hsub1, hvalI']
    have himkC : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) qFrMkC = some (quotMkVal V ψ') := by
      simp only [qFrMkC, interpExpr, hfindMk', quotMkA,
        ConstantInfo.toConstantVal, List.length_cons, List.length_nil,
        reduceIte, hsub1, hvalMk']
    have hifvA : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) qFrA = some A := by
      simp [qFrA, interpExpr, updV]
    have hifvR : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) qFrR = some R := by
      simp [qFrR, interpExpr, updV]
    have hifvB : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) qiFrB = some B := by
      simp [qiFrB, interpExpr, updV]
    have hifvMk : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) qiFrMk = some mk := by
      simp [qiFrMk, interpExpr, updV]
    have hifva : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) qiFra = some a := by
      simp [qiFra, interpExpr, updV]
    have hip1 : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) (.app qiFrRec qFrA) =
        some (SetTheory.app (quotIndVal V ψ') A) := by
      rw [interpExpr, hirec, hifvA]
    have hip2 : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) (.app (.app qiFrRec qFrA) qFrR) =
        some (SetTheory.app (SetTheory.app (quotIndVal V ψ') A) R) := by
      rw [interpExpr, hip1, hifvR]
    have hip3 : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) (.app (.app (.app qiFrRec qFrA) qFrR) qiFrB) =
        some (SetTheory.app (SetTheory.app (SetTheory.app
          (quotIndVal V ψ') A) R) B) := by
      rw [interpExpr, hip2, hifvB]
    have hip4 : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a)
        (.app (.app (.app (.app qiFrRec qFrA) qFrR) qiFrB) qiFrMk) =
        some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (quotIndVal V ψ') A) R) B) mk) := by
      rw [interpExpr, hip3, hifvMk]
    have hiq1 : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) (.app qFrMkC qFrA) =
        some (SetTheory.app (quotMkVal V ψ') A) := by
      rw [interpExpr, himkC, hifvA]
    have hiq2 : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) (.app (.app qFrMkC qFrA) qFrR) =
        some (SetTheory.app (SetTheory.app (quotMkVal V ψ') A) R) := by
      rw [interpExpr, hiq1, hifvR]
    have hiq3 : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) (.app (.app (.app qFrMkC qFrA) qFrR) qiFra) =
        some (SetTheory.app (SetTheory.app (SetTheory.app
          (quotMkVal V ψ') A) R) a) := by
      rw [interpExpr, hiq2, hifva]
    obtain ⟨T, hT, hmem⟩ := quotInd_key (cval := cval) (env := env)
      (ψ := ψ') hfindQ hvalQ hfindMk hvalMk
    rw [interp_quotInd_type hfindQ hvalQ hfindMk hvalMk] at hT
    obtain rfl := Option.some.inj hT
    have hm1 := app_mem hmem hA (fun A' hA' => qiT1_univ hA')
    have hm2 := app_mem hm1 hR (fun R' hR' => qiT2_univ hA hR')
    have hm3 := app_mem hm2 hB (fun B' hB' => qiT3_univ hA hR hB')
    have hm4 := app_mem hm3 hmk (fun _ _ => qiT4_univ hA hR hB)
    have hqv : SetTheory.app (SetTheory.app (SetTheory.app
        (quotMkVal V ψ') A) R) a ∈ˢ
        SetTheory.app (SetTheory.app (quotVal V ψ') A) R := by
      rw [quotVal_app₂' hA hR, quotMkVal_app₃' hA hR ha]
      exact quotClass_mem ha
    refine TowerOk.nil (w := pt) ?_ ?_ ?_
    · rw [interpExpr, hip4, hiq3]
      show some (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (quotIndVal V ψ') A) R) B) mk)
        (SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ') A)
          R) a)) = some pt
      rw [show (quotIndVal V ψ' : V) = pt from by
        simp only [quotIndVal]
        refine lamC_of_forall fun A' hA' => ?_
        refine lamC_of_forall fun R' hR' => ?_
        refine lamC_of_forall fun B' hB' => ?_
        refine lamC_of_forall fun mk' hmk' => ?_
        exact lamC_of_forall fun q' hq' => rfl]
      simp only [app_pt]
    · show interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 R) 2 B)
          3 mk) 4 a) (.app qiFrMk qiFra) = some pt
      rw [interpExpr, hifvMk, hifva]
      show some (SetTheory.app mk a) = some pt
      rw [hmkpt, app_pt]
    · simp only [AnnotOk, qiFrRec, qFrMkC, qFrA, qFrR, qFrTyR, qiFrB,
        qiFrTyB, qiFrMk, qiFrTyMk, qiFra]
      exact ⟨⟨⟨⟨⟨trivial, trivial,
          quotIndVal V ψ', A, 0, univ (ψ' uN), _,
          hirec, hifvA, hmem, hA, fun A' hA' => qiT1_univ hA'⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
        SetTheory.app (quotIndVal V ψ') A, R, 0, relSpace V (ψ' uN) A, _,
          hip1, hifvR, hm1, hR, fun R' hR' => qiT2_univ hA hR'⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
        SetTheory.app (SetTheory.app (quotIndVal V ψ') A) R, B, 0,
          pi 1 (SetTheory.app (SetTheory.app (quotVal V ψ') A) R)
            (fun _ => univ 0), _,
          hip2, hifvB, hm2, hB, fun B' hB' => qiT3_univ hA hR hB'⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
        SetTheory.app (SetTheory.app (SetTheory.app (quotIndVal V ψ') A)
          R) B, mk, 0,
          pi 0 A (fun a' => SetTheory.app B (SetTheory.app (SetTheory.app
            (SetTheory.app (quotMkVal V ψ') A) R) a')), _,
          hip3, hifvMk, hm3, hmk, fun _ _ => qiT4_univ hA hR hB⟩,
        ⟨⟨⟨trivial, trivial,
          quotMkVal V ψ', A, ψ' uN, univ (ψ' uN),
          (fun X => pi (ψ' uN) (relSpace V (ψ' uN) X) fun R' =>
            pi (ψ' uN) X fun _ => quotSet (ψ' uN) X R'),
          himkC, hifvA, quotMkVal_mem', hA,
          fun X hX => quotMkD1_univ' hX⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
        SetTheory.app (quotMkVal V ψ') A, R, ψ' uN,
          relSpace V (ψ' uN) A,
          (fun R' => pi (ψ' uN) A fun _ => quotSet (ψ' uN) A R'),
          hiq1, hifvR, quotMkVal_app_mem' hA, hR,
          fun R' _ => quotMkD2_univ' hA⟩,
        trivial,
        SetTheory.app (SetTheory.app (quotMkVal V ψ') A) R, a, ψ' uN, A,
          (fun _ => quotSet (ψ' uN) A R),
          hiq2, hifva, quotMkVal_app₂_mem' hA hR, ha,
          fun _ _ => quotSet_mem_univ hA⟩,
        SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (quotIndVal V ψ') A) R) B) mk,
        SetTheory.app (SetTheory.app (SetTheory.app (quotMkVal V ψ') A)
          R) a,
        0, SetTheory.app (SetTheory.app (quotVal V ψ') A) R,
        (fun q => SetTheory.app B q),
        hip4, hiq3, hm4, hqv,
        fun q hq => app_mem hB hq (fun _ _ => univ_mem_univ 0)⟩

end Setlec
