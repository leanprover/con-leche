import Setlec.Model.BasisInstall
import Setlec.Model.Basis.Glue

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

variable (V) in
/-- The interpretation of the `Quot.lift` rule rhs, as a value (the
lam tags are the raw annotation evaluations; the invariance domain
carries the `Eq`-value form of the equation fibre). -/
noncomputable def quotLiftRhsVal (ψ : Name → Nat) : V :=
  SetTheory.lam (qlAI (ψ uN) (ψ vN)) (univ (ψ uN)) fun A =>
    SetTheory.lam (qlRI (ψ uN) (ψ vN)) (relSpace V (ψ uN) A) fun R =>
      SetTheory.lam (qlBI (ψ uN) (ψ vN)) (univ (ψ vN)) fun B =>
        SetTheory.lam (qlF (ψ uN) (ψ vN)) (pi (ψ vN) A fun _ => B)
            fun f =>
          SetTheory.lam (qlH (ψ uN) (ψ vN))
              (pi 0 A fun a => pi 0 A fun b =>
                pi 0 (SetTheory.app (SetTheory.app R a) b) fun _ =>
                  SetTheory.app (SetTheory.app (SetTheory.app
                    (eqVal V (Level.substFn ψ [uN] [.param vN])) B)
                    (SetTheory.app f a)) (SetTheory.app f b))
              fun _h =>
            SetTheory.lam (ψ vN) A fun a => SetTheory.app f a

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
    quotLiftRhsVal, qlAI, qlRI, qlBI, qlF, qlH,
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
    (pi 0 A fun a => pi 0 A fun b =>
      pi 0 (SetTheory.app (SetTheory.app R a) b) fun _ =>
        SetTheory.app (SetTheory.app (SetTheory.app
          (eqVal V (Level.substFn ψ [uN] [.param vN])) B)
          (SetTheory.app f a)) (SetTheory.app f b)) =
      quotInvSpace V A R f := by
  unfold quotInvSpace
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
        simp only [quotMkVal, hu]; exact lam_zero,
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

/-! Domain extraction from the tower's typing slots. -/

private theorem qlVal_dom {u v : Nat} {C : V → V → V}
    {G : V → V → V → V → V} {vE : Nat} {A1 : V} {B1 : V → V} {x : V}
    (h : (qlVal V u v C G : V) ∈ˢ pi vE A1 B1) (hx : x ∈ˢ A1) :
    x ∈ˢ univ u := by
  simp only [qlVal] at h
  exact lam_dom_of_ne h
    (max_ne_zero_r' (max_ne_zero_l (Nat.succ_ne_zero v))) x hx

private theorem qlL1_dom {u v : Nat} {C : V → V → V}
    {G : V → V → V → V → V} {Av : V} {vE : Nat} {A2 : V} {B2 : V → V}
    {x : V} (h : qlL1 V u v C G Av ∈ˢ pi vE A2 B2) (hx : x ∈ˢ A2) :
    x ∈ˢ relSpace V u Av := by
  simp only [qlL1] at h
  exact lam_dom_of_ne h (max_ne_zero_l (Nat.succ_ne_zero v)) x hx

private theorem qlL2_dom {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {G : V → V → V → V → V} {Av Rv : V} {vE : Nat} {A3 : V}
    {B3 : V → V} {x : V} (h : qlL2 V u v C G Av Rv ∈ˢ pi vE A3 B3)
    (hx : x ∈ˢ A3) : x ∈ˢ univ v := by
  simp only [qlL2] at h
  exact lam_dom_of_ne h (max_ne_zero_r' h0) x hx

private theorem qlL3_dom {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {G : V → V → V → V → V} {Av Rv Bv : V} {vE : Nat} {A4 : V}
    {B4 : V → V} {x : V} (h : qlL3 V u v C G Av Rv Bv ∈ˢ pi vE A4 B4)
    (hx : x ∈ˢ A4) : x ∈ˢ pi v Av fun _ => Bv := by
  simp only [qlL3] at h
  exact lam_dom_of_ne h (max_ne_zero_r' h0) x hx

private theorem qlL4_dom {u v : Nat} (h0 : v ≠ 0) {C : V → V → V}
    {G : V → V → V → V → V} {Av Rv fv : V} {vE : Nat} {A5 : V}
    {B5 : V → V} {x : V} (h : qlL4 V u v C G Av Rv fv ∈ˢ pi vE A5 B5)
    (hx : x ∈ˢ A5) : x ∈ˢ quotInvSpace V Av Rv fv := by
  simp only [qlL4] at h
  exact lam_dom_of_ne h (max_ne_zero_r' h0) x hx

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
  simp only [quotLiftRhsVal, qlVal, qlL1, qlL2, qlL3, qlL4, qlL5,
    qlF_eq, qlBI_eq, hq, hr, ha]
  refine lam_congr fun A _ => ?_
  refine lam_congr fun R _ => ?_
  refine lam_congr fun B hB' => ?_
  refine lam_congr fun f hf' => ?_
  rw [qlInvEq hB' hf']

/-- Claims packaging for the `Quot.lift` rule: from the recursor
application chain's typing slots, the major's constructor form (with
the kernel's parameter and level checks), and the constructor field's
membership `hav`, produce the rule-rhs interpretation, the fold
equation, and the typing slots of the reduct's application chain. -/
theorem quotLiftIota_claims {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    {ψj : Name → Nat} {Av Rv Bv fv hv tv Av' Rv' av : V}
    {vE1 vE2 vE3 vE4 vE5 vE6 : Nat} {A1 A2 A3 A4 A5 A6 : V}
    {B1 B2 B3 B4 B5 B6 : V → V}
    (h1 : (quotLiftVal V ψ : V) ∈ˢ pi vE1 A1 B1) (hA : Av ∈ˢ A1)
    (h2 : SetTheory.app (quotLiftVal V ψ) Av ∈ˢ pi vE2 A2 B2)
    (hR : Rv ∈ˢ A2)
    (h3 : SetTheory.app (SetTheory.app (quotLiftVal V ψ) Av) Rv ∈ˢ
      pi vE3 A3 B3)
    (hB : Bv ∈ˢ A3)
    (h4 : SetTheory.app (SetTheory.app (SetTheory.app (quotLiftVal V ψ)
      Av) Rv) Bv ∈ˢ pi vE4 A4 B4)
    (hf : fv ∈ˢ A4)
    (h5 : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
      (quotLiftVal V ψ) Av) Rv) Bv) fv ∈ˢ pi vE5 A5 B5)
    (hh : hv ∈ˢ A5)
    (_h6 : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
      (SetTheory.app (quotLiftVal V ψ) Av) Rv) Bv) fv) hv ∈ˢ
      pi vE6 A6 B6)
    (_ht : tv ∈ˢ A6)
    (htv : tv = SetTheory.app (SetTheory.app (SetTheory.app
      (quotMkVal V ψj) Av') Rv') av)
    (hpA : Av' = Av) (hpR : Rv' = Rv) (hlev : ψj uN = ψ uN)
    (hav : av ∈ˢ Av') :
    ∃ R, interpClosed V cval env ψ quotLiftRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (quotLiftVal V ψ) Av) Rv) Bv) fv)
        hv) tv =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app R Av) Rv) Bv) fv) hv) av ∧
      ChainSlots V R [Av, Rv, Bv, fv, hv, av] := by
  rw [hpA, hpR] at htv
  rw [hpA] at hav
  by_cases h0 : ψ vN = 0
  · -- Prop collapse: both sides of the fold are the proof point
    have hRpt : (quotLiftRhsVal V ψ : V) = pt := by
      simp only [quotLiftRhsVal]
      rw [show qlAI (ψ uN) (ψ vN) = 0 from by rw [qlAI_eq, if_pos h0]]
      exact lam_zero
    have hVpt : (quotLiftVal V ψ : V) = pt := by
      simp only [quotLiftVal, h0, reduceIte]
      exact lam_zero
    refine ⟨_, interp_quotLift_rhs hfindE hvalE, ?_, ?_⟩
    · rw [hRpt, hVpt]
      simp only [app_pt]
    · rw [hRpt]
      simp only [ChainSlots, app_pt]
      exact ⟨⟨0, A1, fun _ => unitSet, pt_mem_pi_unit (V := V), hA,
          fun _ _ => unitSet_mem_univ 0⟩,
        ⟨0, A2, fun _ => unitSet, pt_mem_pi_unit (V := V), hR,
          fun _ _ => unitSet_mem_univ 0⟩,
        ⟨0, A3, fun _ => unitSet, pt_mem_pi_unit (V := V), hB,
          fun _ _ => unitSet_mem_univ 0⟩,
        ⟨0, A4, fun _ => unitSet, pt_mem_pi_unit (V := V), hf,
          fun _ _ => unitSet_mem_univ 0⟩,
        ⟨0, A5, fun _ => unitSet, pt_mem_pi_unit (V := V), hh,
          fun _ _ => unitSet_mem_univ 0⟩,
        ⟨0, Av, fun _ => unitSet, pt_mem_pi_unit (V := V), hav,
          fun _ _ => unitSet_mem_univ 0⟩,
        trivial⟩
  · -- data: fold through the tower and reduce with `quotLift_beta`
    have hCL : ∀ A R', A ∈ˢ univ (ψ uN) → R' ∈ˢ relSpace V (ψ uN) A →
        quotSet (ψ uN) A R' ∈ˢ univ (ψ uN) :=
      fun A R' hA' _ => quotSet_mem_univ hA'
    have hGL : QlG V (ψ uN) (ψ vN) (fun A R' => quotSet (ψ uN) A R')
        (fun A R' f q =>
          SetTheory.app (quotLift (ψ uN) (ψ vN) A R' f) q) := by
      intro A R' B f h q hA' hR' hB' hf' hh' hq'
      exact app_mem (quotLift_mem hA' hf' (inv_of_invSpace' hA' hR' hh'))
        hq' (fun _ _ => hB')
    have hCR : ∀ A R', A ∈ˢ univ (ψ uN) → R' ∈ˢ relSpace V (ψ uN) A →
        A ∈ˢ univ (ψ uN) := fun _ _ hA' _ => hA'
    have hGR : QlG V (ψ uN) (ψ vN) (fun A _ => A)
        (fun _ _ f a => SetTheory.app f a) := by
      intro A R' B f h q _ _ hB' hf' _ hq'
      exact app_mem hf' hq' (fun _ _ => hB')
    have hVeq := quotLiftVal_eq_qlVal (V := V) (ψ := ψ) h0
    -- canonical memberships from the value chain's slots
    rw [hVeq] at h1 h2 h3 h4 h5
    have hAc : Av ∈ˢ univ (ψ uN) := qlVal_dom h1 hA
    rw [qlVal_app1 h0 hGL hCL hAc] at h2 h3 h4 h5
    have hRc : Rv ∈ˢ relSpace V (ψ uN) Av := qlL1_dom h2 hR
    rw [qlL1_app h0 hGL hCL hAc hRc] at h3 h4 h5
    have hBc : Bv ∈ˢ univ (ψ vN) := qlL2_dom h0 h3 hB
    rw [qlL2_app h0 hGL hCL hAc hRc hBc] at h4 h5
    have hfc : fv ∈ˢ pi (ψ vN) Av (fun _ => Bv) := qlL3_dom h0 h4 hf
    rw [qlL3_app h0 hGL hCL hAc hRc hBc hfc] at h5
    have hhc : hv ∈ˢ quotInvSpace V Av Rv fv := qlL4_dom h0 h5 hh
    -- the constructor spine is the class of the packed element
    have htcl : tv = quotClass (ψ uN) Av Rv av := by
      rw [htv, quotMkVal_lev hlev, quotMkVal_app₃' hAc hRc hav]
    have hinv := inv_of_invSpace' hAc hRc hhc
    -- the left fold
    have hfoldL : SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (SetTheory.app (quotLiftVal V ψ)
        Av) Rv) Bv) fv) hv) tv = SetTheory.app fv av := by
      rw [hVeq, qlVal_app1 h0 hGL hCL hAc, qlL1_app h0 hGL hCL hAc hRc,
        qlL2_app h0 hGL hCL hAc hRc hBc,
        qlL3_app h0 hGL hCL hAc hRc hBc hfc,
        qlL4_app h0 hGL hCL hAc hRc hBc hfc hhc, htcl,
        qlL5_app (quotClass_mem hav)
          (fun q hq => app_mem (quotLift_mem hAc hfc hinv) hq
            (fun _ _ => hBc)) hBc]
      exact quotLift_beta hAc hav hinv
    have hReq := quotLiftRhsVal_eq_qlVal (V := V) (ψ := ψ) h0
    refine ⟨_, interp_quotLift_rhs hfindE hvalE, ?_, ?_⟩
    · -- the fold: the right chain also computes to `app fv av`
      rw [hfoldL, hReq, qlVal_app1 h0 hGR hCR hAc,
        qlL1_app h0 hGR hCR hAc hRc, qlL2_app h0 hGR hCR hAc hRc hBc,
        qlL3_app h0 hGR hCR hAc hRc hBc hfc,
        qlL4_app h0 hGR hCR hAc hRc hBc hfc hhc,
        qlL5_app hav (fun q hq => app_mem hfc hq (fun _ _ => hBc)) hBc]
    · -- the reduct's chain slots
      rw [hReq]
      simp only [ChainSlots]
      rw [qlVal_app1 h0 hGR hCR hAc, qlL1_app h0 hGR hCR hAc hRc,
        qlL2_app h0 hGR hCR hAc hRc hBc,
        qlL3_app h0 hGR hCR hAc hRc hBc hfc,
        qlL4_app h0 hGR hCR hAc hRc hBc hfc hhc]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
      · exact ⟨Nat.max (Nat.max (ψ uN) 1)
            (Nat.max (ψ vN + 1) (Nat.max (ψ uN) (ψ vN))),
          univ (ψ uN), fun A => qlD1 V (ψ uN) (ψ vN) (fun A' _ => A') A,
          qlVal_mem hGR, hAc,
          fun A hA' => qlD1_univ h0 hA' (fun _ _ => hA')⟩
      · refine ⟨Nat.max (ψ vN + 1) (Nat.max (ψ uN) (ψ vN)),
          relSpace V (ψ uN) Av,
          fun R' => qlD2 V (ψ uN) (ψ vN) (fun A' _ => A') Av R',
          ?_, hRc, fun R' hR' => qlD2_univ h0 hAc hR' hAc⟩
        have := qlL1_mem (A := Av) hGR hAc
        simpa only [qlD1] using this
      · refine ⟨Nat.max (ψ uN) (ψ vN), univ (ψ vN),
          fun B => qlD3 V (ψ uN) (ψ vN) (fun A' _ => A') Av Rv B,
          ?_, hBc, fun B hB' => qlD3_univ h0 hAc hRc hAc hB'⟩
        have := qlL2_mem (A := Av) (R := Rv) hGR hAc hRc
        simpa only [qlD2] using this
      · refine ⟨Nat.max (ψ uN) (ψ vN), pi (ψ vN) Av fun _ => Bv,
          fun f => qlD4 V (ψ uN) (ψ vN) (fun A' _ => A') Av Rv Bv f,
          ?_, hfc, fun f _ => qlD4_univ h0 hAc hRc hAc hBc⟩
        have := qlL3_mem (A := Av) (R := Rv) (B := Bv) hGR hAc hRc hBc
        simpa only [qlD3] using this
      · refine ⟨Nat.max (ψ uN) (ψ vN), quotInvSpace V Av Rv fv,
          fun _ => qlD5 V (ψ vN) (fun A' _ => A') Av Rv Bv,
          ?_, hhc, fun _ _ => qlD5_univ h0 hAc hBc⟩
        have := qlL4_mem (A := Av) (R := Rv) (B := Bv) (f := fv)
          hGR hAc hRc hBc hfc
        simpa only [qlD4] using this
      · refine ⟨ψ vN, Av, fun _ => Bv, ?_, hav, fun _ _ => hBc⟩
        have := qlL5_mem (V := V) (v := ψ vN) (A := Av) (R := Rv)
          (B := Bv) (f := fv) (C := fun A' _ => A')
          (G := fun _ _ f a => SetTheory.app f a)
          (fun q hq => app_mem hfc hq (fun _ _ => hBc))
        simpa only [qlD5] using this

/-- Claims packaging for the `Quot.ind` rule.  Both sides of the fold
are the proof point (the motive is propositional), and the reduct's
chain slots are trivial Prop slots over the given argument
memberships.  `hav` is the constructor field's membership in the
(arbitrary) domain the consumer has for it. -/
theorem quotIndIota_claims {cval : ConstVal V}
    (hfindQ : env.find? quotName = some quotA)
    (hvalQ : ∀ ψ' : Name → Nat, cval quotName ψ' = quotVal V ψ')
    (hfindMk : env.find? quotMkName = some quotMkA)
    (hvalMk : ∀ ψ' : Name → Nat, cval quotMkName ψ' = quotMkVal V ψ')
    {Av Rv Bv mkv tv av Cv : V} {vE1 vE2 vE3 vE4 vE5 : Nat}
    {A1 A2 A3 A4 A5 : V} {B1 B2 B3 B4 B5 : V → V}
    (_h1 : (quotIndVal V ψ : V) ∈ˢ pi vE1 A1 B1) (hA : Av ∈ˢ A1)
    (_h2 : SetTheory.app (quotIndVal V ψ) Av ∈ˢ pi vE2 A2 B2)
    (hR : Rv ∈ˢ A2)
    (_h3 : SetTheory.app (SetTheory.app (quotIndVal V ψ) Av) Rv ∈ˢ
      pi vE3 A3 B3)
    (hB : Bv ∈ˢ A3)
    (_h4 : SetTheory.app (SetTheory.app (SetTheory.app (quotIndVal V ψ)
      Av) Rv) Bv ∈ˢ pi vE4 A4 B4)
    (hmk : mkv ∈ˢ A4)
    (_h5 : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
      (quotIndVal V ψ) Av) Rv) Bv) mkv ∈ˢ pi vE5 A5 B5)
    (_ht : tv ∈ˢ A5)
    (hav : av ∈ˢ Cv) :
    ∃ R, interpClosed V cval env ψ quotIndRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (quotIndVal V ψ) Av) Rv) Bv) mkv) tv =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app R Av) Rv) Bv) mkv) av ∧
      ChainSlots V R [Av, Rv, Bv, mkv, av] := by
  have hRpt : (quotIndRhsVal V ψ : V) = pt := by
    simp only [quotIndRhsVal]
    exact lam_zero
  have hIpt : (quotIndVal V ψ : V) = pt := by
    simp only [quotIndVal]
    exact lam_zero
  refine ⟨_, interp_quotInd_rhs hfindQ hvalQ hfindMk hvalMk, ?_, ?_⟩
  · rw [hRpt, hIpt]
    simp only [app_pt]
  · rw [hRpt]
    simp only [ChainSlots, app_pt]
    exact ⟨⟨0, A1, fun _ => unitSet, pt_mem_pi_unit (V := V), hA,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A2, fun _ => unitSet, pt_mem_pi_unit (V := V), hR,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A3, fun _ => unitSet, pt_mem_pi_unit (V := V), hB,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A4, fun _ => unitSet, pt_mem_pi_unit (V := V), hmk,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, Cv, fun _ => unitSet, pt_mem_pi_unit (V := V), hav,
        fun _ _ => unitSet_mem_univ 0⟩,
      trivial⟩

end Setlec
