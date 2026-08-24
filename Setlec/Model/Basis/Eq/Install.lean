import Setlec.Model.Basis.Util

/-!
# `Eq` basis block: interpretation and `hkey` obligations
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-- Interpretation of `Eq`'s pinned type, computed. -/
theorem interp_eq_type {cval : ConstVal V} :
    interpClosed V cval env ψ eqA.toConstantVal.type =
      some (pi (Nat.max (ψ uN) (Nat.max (ψ uN) 1)) (univ (ψ uN)) fun A =>
        pi (Nat.max (ψ uN) 1) A fun _ =>
          pi 1 A fun _ => univ 0) := by
  simp only [interpClosed, eqA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD]
  simp [interpExpr, Expr.instantiate1, updV, uN]
  try rfl

/-- The fibre family of `Eq`'s value, in its universe. -/
theorem eq_fibre_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    (pi (Nat.max (ψ uN) 1) A fun _ => pi 1 A fun _ => univ 0) ∈ˢ
      univ (Nat.max (ψ uN) (Nat.max (ψ uN) 1)) := by
  have hmem := pi_mem_univ (u := ψ uN) (v := Nat.max (ψ uN) 1)
    (B := fun _ => pi 1 A (fun _ => univ 0)) hA
    (fun x _ => pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
      hA (fun _ _ => univ_mem_univ 0))
  have h1 : 1 ≤ Nat.max (ψ uN) 1 := Nat.le_max_right _ _
  have hne : Nat.max (ψ uN) 1 ≠ 0 := fun hc => absurd (hc ▸ h1) (by decide)
  rwa [if_neg hne] at hmem

/-- `Eq`'s value is a member of its pi-type (the shape app reasoning
uses). -/
theorem eqVal_mem :
    (eqVal V ψ : V) ∈ˢ pi (Nat.max (ψ uN) (Nat.max (ψ uN) 1)) (univ (ψ uN))
      (fun A => pi (Nat.max (ψ uN) 1) A fun _ => pi 1 A fun _ => univ 0) := by
  simp only [eqVal]
  refine lam_mem (V := V) (B := fun A => pi (Nat.max (ψ uN) 1) A fun _ =>
    pi 1 A fun _ => univ 0) fun A hA => ?_
  refine lam_mem (V := V) (B := fun _ => pi 1 A fun _ => univ 0) fun x hx => ?_
  refine lam_mem (V := V) (B := fun _ => univ 0) fun y hy => ?_
  exact eqv_mem_univ x y

/-- `Eq`'s value inhabits its type. -/
theorem eq_key {cval : ConstVal V} :
    ∃ T, interpClosed V cval env ψ eqA.toConstantVal.type = some T ∧
      eqVal V ψ ∈ˢ T :=
  ⟨_, interp_eq_type, eqVal_mem⟩

/-- Applying `Eq`'s value to a domain computes to the binary lam pack. -/
theorem eqVal_app {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (eqVal V ψ) A =
      SetTheory.lam (Nat.max (ψ uN) 1) A fun x =>
        SetTheory.lam 1 A fun y => eqv x y := by
  simp only [eqVal]
  exact app_lam
    (B := fun X => pi (Nat.max (ψ uN) 1) X fun _ => pi 1 X fun _ => univ 0) hA
    (fun X hX => lam_mem (V := V) (B := fun _ => pi 1 X fun _ => univ 0)
      fun x _ => lam_mem (V := V) (B := fun _ => univ 0)
        fun y _ => eqv_mem_univ x y)
    (fun X hX => eq_fibre_mem hX)

theorem eqVal_app_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (eqVal V ψ) A ∈ˢ
      pi (Nat.max (ψ uN) 1) A (fun _ => pi 1 A fun _ => univ 0) := by
  rw [eqVal_app hA]
  exact lam_mem (V := V) (B := fun _ => pi 1 A fun _ => univ 0)
    fun x _ => lam_mem (V := V) (B := fun _ => univ 0)
      fun y _ => eqv_mem_univ x y

/-- Applying `Eq`'s value to a domain and a point. -/
theorem eqVal_app₂ {A a : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (eqVal V ψ) A) a =
      SetTheory.lam 1 A fun y => eqv a y := by
  rw [eqVal_app hA]
  exact app_lam (B := fun _ => pi 1 A fun _ => univ 0) ha
    (fun x _ => lam_mem (V := V) (B := fun _ => univ 0)
      fun y _ => eqv_mem_univ x y)
    (fun x _ => by
      exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0) hA
        (fun _ _ => univ_mem_univ 0))

theorem eqVal_app₂_mem {A a : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (eqVal V ψ) A) a ∈ˢ
      pi 1 A (fun _ => univ 0) := by
  rw [eqVal_app₂ hA ha]
  exact lam_mem (V := V) (B := fun _ => univ 0) fun y _ => eqv_mem_univ a y

/-- The full application of `Eq`'s value is the equality truth value. -/
theorem eqVal_app₃ {A a b : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A)
    (hb : b ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b =
      eqv a b := by
  rw [eqVal_app₂ hA ha]
  exact app_lam (B := fun _ => univ 0) hb
    (fun y _ => eqv_mem_univ a y)
    (fun y _ => univ_mem_univ 0)

/-- `Eq`'s type carries truthful annotations. -/
theorem annotOk_eq_type {cval : ConstVal V} :
    AnnotOk V cval env ψ 0 (rho0 V) eqA.toConstantVal.type := by
  simp only [eqA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, Nat.max (ψ uN) (Nat.max (ψ uN) 1), ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · try simp only [Expr.instantiate1, AnnotOk]
    refine ⟨by simp only [reduceIte]; simp [AnnotOk], Nat.max (ψ uN) 1, ?_⟩
    intro x Sx hSx hxmem
    have hSx' : Sx = A := by
      simp only [interpExpr, updV, Expr.instantiate1, reduceIte,
        Option.some.injEq] at hSx
      exact hSx.symm
    rw [hSx'] at hxmem
    refine ⟨?_, ?_⟩
    · try simp only [Expr.instantiate1, AnnotOk]
      refine ⟨by simp only [reduceIte]; simp [Expr.instantiate1, AnnotOk],
        1, ?_⟩
      intro y Sy hSy hymem
      refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
      refine ⟨univ 0, ?_, ?_⟩
      · simp [Expr.instantiate1, interpExpr, Level.eval]
      · exact univ_mem_univ 0
    · refine ⟨pi 1 A (fun _ => univ 0), ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
      · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
          hAmem (fun _ _ => univ_mem_univ 0)
  · refine ⟨pi (Nat.max (ψ uN) 1) A (fun _ => pi 1 A (fun _ => univ 0)), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, uN]
      try rfl
    · have hmem := pi_mem_univ (u := ψ uN) (v := Nat.max (ψ uN) 1)
        (B := fun _ => pi 1 A (fun _ => univ 0)) hAmem
        (fun x _ => pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
          hAmem (fun _ _ => univ_mem_univ 0))
      have h1 : 1 ≤ Nat.max (ψ uN) 1 := Nat.le_max_right _ _
      have hne : Nat.max (ψ uN) 1 ≠ 0 := fun hc => absurd (hc ▸ h1) (by decide)
      rw [if_neg hne] at hmem
      exact hmem

/-- `Eq.refl`'s value is a member of the reflexivity pi-type. -/
theorem eqReflVal_mem :
    (eqReflVal V ψ : V) ∈ˢ pi 0 (univ (ψ uN))
      (fun A => pi 0 A fun a => eqv a a) := by
  simp only [eqReflVal]
  refine lam_mem (V := V) (B := fun A => pi 0 A fun a => eqv a a)
    fun A hA => ?_
  exact lam_mem (V := V) (B := fun a => eqv a a) fun a _ => pt_mem_eqv_self a

/-- Applying `Eq.refl`'s value to a domain. -/
theorem eqReflVal_app {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (eqReflVal V ψ) A = SetTheory.lam 0 A fun _ => pt := by
  simp only [eqReflVal]
  exact app_lam (B := fun X => pi 0 X fun a => eqv a a) hA
    (fun X _ => lam_mem (V := V) (B := fun a => eqv a a)
      fun a _ => pt_mem_eqv_self a)
    (fun X hX => pi_mem_univ (v := 0) hX (fun a _ => eqv_mem_univ a a))

/-- The full application of `Eq.refl`'s value is the proof point. -/
theorem eqReflVal_app₂ {A a : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a = pt := by
  rw [eqReflVal_app hA]
  exact app_lam (B := fun x => eqv x x) ha
    (fun x _ => pt_mem_eqv_self x)
    (fun x _ => eqv_mem_univ x x)

theorem eqReflVal_app_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (eqReflVal V ψ) A ∈ˢ pi 0 A (fun x => eqv x x) := by
  rw [eqReflVal_app hA]
  exact lam_mem (V := V) (B := fun x => eqv x x) fun x _ => pt_mem_eqv_self x

/-- Interpretation of `Eq.refl`'s pinned type, computed (both pis are
Prop-level: the codomain annotations are `0` and `imax u 0`). -/
theorem interp_eqRefl_type {cval : ConstVal V}
    (hfind : env.find? eqName = some eqA)
    (hval : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ') :
    interpClosed V cval env ψ eqReflA.toConstantVal.type =
      some (pi 0 (univ (ψ uN)) fun A => pi 0 A fun a =>
        SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) a) := by
  have hfind' : env.find? (Name.anonymous.str "Eq") = some eqA := hfind
  have hval' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hval
  simp only [interpClosed, eqReflA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD, hfind', hval', eqA,
    List.length_cons, List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, Expr.instantiate1, updV, uN]
  try rfl

/-- `Eq.refl`'s value inhabits its type. -/
theorem eqRefl_key {cval : ConstVal V}
    (hfind : env.find? eqName = some eqA)
    (hval : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ') :
    ∃ T, interpClosed V cval env ψ eqReflA.toConstantVal.type = some T ∧
      eqReflVal V ψ ∈ˢ T := by
  refine ⟨_, interp_eqRefl_type hfind hval, ?_⟩
  simp only [eqReflVal]
  refine lam_mem (V := V) (B := fun A => pi 0 A fun a =>
    SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) a)
    fun A hA => ?_
  refine lam_mem (V := V) (B := fun a =>
    SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) a)
    fun a ha => ?_
  rw [eqVal_app₃ hA ha ha]
  exact pt_mem_eqv_self a

/-- `Eq.refl`'s type carries truthful annotations. -/
theorem annotOk_eqRefl_type {cval : ConstVal V}
    (hfind : env.find? eqName = some eqA)
    (hval : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) eqReflA.toConstantVal.type := by
  have hfind' : env.find? (Name.anonymous.str "Eq") = some eqA := hfind
  have hval' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hval
  simp only [eqReflA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, 0, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · -- the inner `∀ (a : α), Eq α a a` (codomain annotation `0`)
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨trivial, 0, ?_⟩
    intro x Sx hSx hxmem
    have hSx' : Sx = A := by
      simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
        Option.some.injEq] at hSx
      exact hSx.symm
    rw [hSx'] at hxmem
    refine ⟨?_, ?_⟩
    · -- annotations of the opened body `Eq α a a`: three app clauses
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
          eqVal V ψ, A, Nat.max (ψ uN) (Nat.max (ψ uN) 1), univ (ψ uN),
          (fun X => pi (Nat.max (ψ uN) 1) X fun _ => pi 1 X fun _ => univ 0),
          ?_, ?_, eqVal_mem, hAmem, fun X hX => eq_fibre_mem hX⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
          SetTheory.app (eqVal V ψ) A, x, Nat.max (ψ uN) 1, A,
          (fun _ => pi 1 A fun _ => univ 0),
          ?_, ?_, eqVal_app_mem hAmem, hxmem, fun y _ => ?_⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
          SetTheory.app (SetTheory.app (eqVal V ψ) A) x, x, 1, A,
          (fun _ => univ 0),
          ?_, ?_, eqVal_app₂_mem hAmem hxmem, hxmem,
          fun y _ => univ_mem_univ 0⟩
      · simp only [interpExpr, hfind', hval', eqA, ConstantInfo.toConstantVal,
          List.length_cons, List.length_nil, reduceIte]
        try rfl
      · simp [interpExpr, Expr.instantiate1, updV]
      · simp [interpExpr, Expr.instantiate1, updV, hfind', hval', eqA,
          ConstantInfo.toConstantVal]
        try rfl
      · simp [interpExpr, Expr.instantiate1, updV]
      · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0) hAmem
          (fun _ _ => univ_mem_univ 0)
      · simp [interpExpr, Expr.instantiate1, updV, hfind', hval', eqA,
          ConstantInfo.toConstantVal]
        try rfl
      · simp [interpExpr, Expr.instantiate1, updV]
    · -- the fibre-universe fact for the inner binder
      refine ⟨SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) x) x,
        ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfind', hval', eqA,
          ConstantInfo.toConstantVal]
        try rfl
      · rw [eqVal_app₃ hAmem hxmem hxmem]
        exact eqv_mem_univ x x
  · -- the fibre-universe fact for the outer binder
    refine ⟨pi 0 A (fun a =>
      SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) a),
      ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfind', hval', eqA,
        ConstantInfo.toConstantVal, Level.eval]
      try rfl
    · have := pi_mem_univ (u := ψ uN) (v := 0)
        (B := fun a => SetTheory.app (SetTheory.app
          (SetTheory.app (eqVal V ψ) A) a) a) hAmem
        (fun a ha => by
          rw [eqVal_app₃ hAmem ha ha]
          exact eqv_mem_univ a a)
      exact this

/-! The evaluations of `Eq.rec`'s binder codomain annotations, in the
raw nested-`if` forms `interpExpr` computes (outermost binder last). -/

def erB (u1 : Nat) : Nat := if u1 = 0 then 0 else u1
def erRefl (u u1 : Nat) : Nat :=
  if erB u1 = 0 then 0 else Nat.max u (erB u1)
def erM (u u1 : Nat) : Nat :=
  if erRefl u u1 = 0 then 0 else Nat.max u1 (erRefl u u1)
def erA (u u1 : Nat) : Nat :=
  if erM u u1 = 0 then 0 else Nat.max u (Nat.max (u1 + 1) (erM u u1))
def erAl (u u1 : Nat) : Nat :=
  if erA u u1 = 0 then 0 else Nat.max u (erA u u1)

/-- Interpretation of `Eq.rec`'s pinned type, computed. -/
theorem interp_eqRec_type {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ') :
    interpClosed V cval env ψ eqRecA.toConstantVal.type =
      some (pi (erAl (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
        pi (erA (ψ uN) (ψ u1N)) A fun a =>
          pi (erM (ψ uN) (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            pi (erRefl (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) fun _ =>
              pi (erB (ψ u1N)) A fun b =>
                pi (ψ u1N)
                  (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
                  fun h => SetTheory.app (SetTheory.app M b) h) := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindR' : env.find? ((Name.anonymous.str "Eq").str "refl") = some eqReflA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "refl") ψ' = eqReflVal V ψ' := hvalR
  simp only [interpClosed, eqRecA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindE', hvalE', hfindR', hvalR', eqA, eqReflA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, u1N,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-! Collapsing the raw annotation evaluations to `eqRecVal`'s tags. -/





theorem erB_eq (u1 : Nat) : erB u1 = u1 := by
  unfold erB
  by_cases h : u1 = 0 <;> simp [h]

theorem erRefl_eq (u u1 : Nat) :
    erRefl u u1 = if u1 = 0 then 0 else Nat.max u u1 := by
  unfold erRefl
  rw [erB_eq]


theorem erM_eq (u u1 : Nat) :
    erM u u1 = if u1 = 0 then 0 else Nat.max u u1 := by
  unfold erM
  rw [erRefl_eq]
  by_cases h : u1 = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_r h)]
    exact max_absorb_r' u u1

theorem erA_eq (u u1 : Nat) :
    erA u u1 = if u1 = 0 then 0 else Nat.max u (u1 + 1) := by
  unfold erA
  rw [erM_eq]
  by_cases h : u1 = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_r h)]
    exact max_eqrec_a u u1

theorem erAl_eq (u u1 : Nat) :
    erAl u u1 = if u1 = 0 then 0 else Nat.max u (u1 + 1) := by
  unfold erAl
  rw [erA_eq]
  by_cases h : u1 = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_r (Nat.succ_ne_zero u1))]
    exact max_absorb_l' u (u1 + 1)

/-- `Eq.rec`'s value inhabits its type (the equality collapse: the
motive's fibre at `b, h` is the fibre at `a, pt`). -/
theorem eqRec_key {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ') :
    ∃ T, interpClosed V cval env ψ eqRecA.toConstantVal.type = some T ∧
      eqRecVal V ψ ∈ˢ T := by
  refine ⟨_, interp_eqRec_type hfindE hvalE hfindR hvalR, ?_⟩
  rw [erAl_eq, erA_eq, erM_eq, erRefl_eq, erB_eq]
  simp only [eqRecVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun a ha => ?_
  have hMS : (pi (ψ u1N + 1) A fun b =>
      pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a := by
    unfold eqRecMSpace
    exact pi_congr fun b hb => by rw [eqVal_app₃ hA ha hb]
  rw [hMS]
  refine lam_mem (V := V) fun M hM => ?_
  rw [eqReflVal_app₂ hA ha]
  refine lam_mem (V := V) fun r hr => ?_
  refine lam_mem (V := V) fun b hb => ?_
  rw [eqVal_app₃ hA ha hb]
  refine lam_mem (V := V) fun h hh => ?_
  obtain rfl : a = b := mem_eqv hh
  obtain rfl : h = pt := mem_univ_zero (eqv_mem_univ a a) hh
  exact hr

/-! Unassociated (raw) forms of the two outermost `Eq.rec` annotation
evaluations (`interp_eqRec_type` states the simp-reassociated forms). -/

def erA₀ (u u1 : Nat) : Nat :=
  if erM u u1 = 0 then 0 else Nat.max (Nat.max u (u1 + 1)) (erM u u1)

theorem erA₀_eq_erA (u u1 : Nat) : erA₀ u u1 = erA u u1 := by
  unfold erA₀ erA
  by_cases h : erM u u1 = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact Nat.max_assoc u (u1 + 1) (erM u u1)

/-- `Eq.rec`'s type carries truthful annotations. -/
theorem annotOk_eqRec_type {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) eqRecA.toConstantVal.type := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindR' : env.find? ((Name.anonymous.str "Eq").str "refl") = some eqReflA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "refl") ψ' = eqReflVal V ψ' := hvalR
  simp only [eqRecA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial,
    (if erA (ψ uN) (ψ u1N) = 0 then 0
      else Nat.max (ψ uN) (erA (ψ uN) (ψ u1N))), ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  -- application facts over the fixed domain `A`, parametric in the point
  have hMSmem : ∀ a', a' ∈ˢ A →
      eqRecMSpace V (ψ u1N) A a' ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
    intro a' ha'
    unfold eqRecMSpace
    exact pi_mem_univ (u := ψ uN) (v := ψ u1N + 1) hAmem
      (fun b hb => by
        exact pi_mem_univ (u := 0) (v := ψ u1N + 1) (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a' b) (fun _ _ => univ_mem_univ (ψ u1N)))
  have happM : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      ∀ b', b' ∈ˢ A →
      SetTheory.app M' b' ∈ˢ pi (ψ u1N + 1) (eqv a' b')
        fun _ => univ (ψ u1N) := by
    intro a' ha' M' hM' b' hb'
    simp only [eqRecMSpace] at hM'
    exact app_mem hM' hb' (fun b hb => by
      exact pi_mem_univ (u := 0) (v := ψ u1N + 1) (B := fun _ => univ (ψ u1N))
        (eqv_mem_univ a' b) (fun _ _ => univ_mem_univ (ψ u1N)))
  have happ2M : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      ∀ b', b' ∈ˢ A → ∀ h', h' ∈ˢ eqv a' b' →
      SetTheory.app (SetTheory.app M' b') h' ∈ˢ univ (ψ u1N) := by
    intro a' ha' M' hM' b' hb' h' hh'
    exact app_mem (happM a' ha' M' hM' b' hb') hh'
      (fun _ _ => univ_mem_univ (ψ u1N))
  -- the interp-form suffix types of the telescope and their universes
  have hMSeq : ∀ a', a' ∈ˢ A →
      (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a' := by
    intro a' ha'
    unfold eqRecMSpace
    exact pi_congr fun b hb => by rw [eqVal_app₃ hAmem ha' hb]
  have hT5 : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      ∀ b', b' ∈ˢ A →
      (pi (ψ u1N)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b')
        fun h' => SetTheory.app (SetTheory.app M' b') h') ∈ˢ
        univ (erB (ψ u1N)) := by
    intro a' ha' M' hM' b' hb'
    rw [eqVal_app₃ hAmem ha' hb']
    exact pi_mem_univ (u := 0) (v := ψ u1N) (eqv_mem_univ a' b')
      (fun h' hh' => happ2M a' ha' M' hM' b' hb' h' hh')
  have hT4 : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      (pi (erB (ψ u1N)) A fun b' =>
        pi (ψ u1N)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b')
          fun h' => SetTheory.app (SetTheory.app M' b') h') ∈ˢ
        univ (erRefl (ψ uN) (ψ u1N)) := by
    intro a' ha' M' hM'
    exact pi_mem_univ (u := ψ uN) (v := erB (ψ u1N)) hAmem
      (fun b' hb' => hT5 a' ha' M' hM' b' hb')
  have hT3 : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      (pi (erRefl (ψ uN) (ψ u1N))
        (SetTheory.app (SetTheory.app M' a')
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a')) fun _ =>
        pi (erB (ψ u1N)) A fun b' =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b')
            fun h' => SetTheory.app (SetTheory.app M' b') h') ∈ˢ
        univ (erM (ψ uN) (ψ u1N)) := by
    intro a' ha' M' hM'
    have hdom : SetTheory.app (SetTheory.app M' a')
        (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a') ∈ˢ
        univ (ψ u1N) := by
      rw [eqReflVal_app₂ hAmem ha']
      exact happ2M a' ha' M' hM' a' ha' pt (pt_mem_eqv_self a')
    exact pi_mem_univ (u := ψ u1N) (v := erRefl (ψ uN) (ψ u1N)) hdom
      (fun r hr => hT4 a' ha' M' hM')
  have hT2 : ∀ a', a' ∈ˢ A →
      (pi (erM (ψ uN) (ψ u1N))
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
          fun _ => univ (ψ u1N)) fun M' =>
        pi (erRefl (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M' a')
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a')) fun _ =>
          pi (erB (ψ u1N)) A fun b' =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b')
              fun h' => SetTheory.app (SetTheory.app M' b') h') ∈ˢ
        univ (erA₀ (ψ uN) (ψ u1N)) := by
    intro a' ha'
    rw [hMSeq a' ha']
    exact pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1))
      (v := erM (ψ uN) (ψ u1N)) (hMSmem a' ha')
      (fun M' hM' => hT3 a' ha' M' hM')
  refine ⟨?_, ?_⟩
  · -- opened `∀ {a : α}, …`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨trivial, erA₀ (ψ uN) (ψ u1N), ?_⟩
    intro a Sa hSa hamem
    simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
      Option.some.injEq] at hSa
    subst hSa
    refine ⟨?_, ?_⟩
    · -- opened `∀ {motive}, …`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨?_, erM (ψ uN) (ψ u1N), ?_⟩
      · -- AnnotOk of the motive space `(b : α) → Eq α a b → Sort u_1`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
          Nat.max 0 (ψ u1N + 1), ?_⟩
        intro b Sb hSb hbmem
        simp [interpExpr, Expr.instantiate1, updV] at hSb
        subst hSb
        refine ⟨?_, ?_⟩
        · -- opened `Eq α a b → Sort u_1`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨?_, ψ u1N + 1, ?_⟩
          · -- AnnotOk of `Eq α a b` (three app clauses)
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                eqVal V ψ, A, Nat.max (ψ uN) (Nat.max (ψ uN) 1), univ (ψ uN),
                (fun X => pi (Nat.max (ψ uN) 1) X fun _ =>
                  pi 1 X fun _ => univ 0),
                ?_, ?_, eqVal_mem, hAmem, fun X hX => eq_fibre_mem hX⟩,
              (by simp [Expr.instantiate1, AnnotOk]),
                SetTheory.app (eqVal V ψ) A, a, Nat.max (ψ uN) 1, A,
                (fun _ => pi 1 A fun _ => univ 0),
                ?_, ?_, eqVal_app_mem hAmem, hamem, fun y _ => ?_⟩,
              (by simp [Expr.instantiate1, AnnotOk]),
                SetTheory.app (SetTheory.app (eqVal V ψ) A) a, b, 1, A,
                (fun _ => univ 0),
                ?_, ?_, eqVal_app₂_mem hAmem hamem, hbmem,
                fun y _ => univ_mem_univ 0⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                eqA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                eqA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
            · exact pi_mem_univ (u := ψ uN) (v := 1) (B := fun _ => univ 0)
                hAmem (fun _ _ => univ_mem_univ 0)
            · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                eqA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
          · intro h Sh hSh hhmem
            refine ⟨trivial, ?_⟩
            refine ⟨univ (ψ u1N), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, Level.eval, u1N]
            · exact univ_mem_univ (ψ u1N)
        · -- fibre-universe of the motive space's `b` binder
          refine ⟨pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            (fun _ => univ (ψ u1N)), ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
              eqA, ConstantInfo.toConstantVal, Level.eval,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl
          · rw [eqVal_app₃ hAmem hamem hbmem]
            exact pi_mem_univ (u := 0) (v := ψ u1N + 1)
              (B := fun _ => univ (ψ u1N)) (eqv_mem_univ a b)
              (fun _ _ => univ_mem_univ (ψ u1N))
      · intro M SM hSM hMmem
        simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
          eqA, ConstantInfo.toConstantVal, Level.eval,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSM
        subst hSM
        have hMmem' : M ∈ˢ eqRecMSpace V (ψ u1N) A a := by
          rw [← hMSeq a hamem]
          exact hMmem
        refine ⟨?_, ?_⟩
        · -- opened `∀ (refl : motive a (Eq.refl α a)), …`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨?_, erRefl (ψ uN) (ψ u1N), ?_⟩
          · -- AnnotOk of `motive a (Eq.refl α a)` (app clauses)
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                (by simp [Expr.instantiate1, AnnotOk]),
                M, a, ψ u1N + 1, A,
                (fun b' => pi (ψ u1N + 1) (eqv a b') fun _ => univ (ψ u1N)),
                ?_, ?_, ?_, hamem, ?_⟩,
              ⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                eqReflVal V ψ, A, 0, univ (ψ uN),
                (fun X => pi 0 X fun x => eqv x x),
                ?_, ?_, eqReflVal_mem, hAmem,
                fun X hX => by
                  exact pi_mem_univ (u := ψ uN) (v := 0) hX
                    (fun x _ => eqv_mem_univ x x)⟩,
              (by simp [Expr.instantiate1, AnnotOk]),
                SetTheory.app (eqReflVal V ψ) A, a, 0, A, (fun x => eqv x x),
                ?_, ?_, eqReflVal_app_mem hAmem, hamem,
                fun x _ => eqv_mem_univ x x⟩,
              SetTheory.app M a,
              SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a,
              ψ u1N + 1, eqv a a, (fun _ => univ (ψ u1N)),
              ?_, ?_, happM a hamem M hMmem' a hamem, ?_,
              fun _ _ => univ_mem_univ (ψ u1N)⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
            · -- M ∈ its space, in the eqv form
              have := hMmem'
              simp only [eqRecMSpace] at this
              exact this
            · intro b' hb'
              exact pi_mem_univ (u := 0) (v := ψ u1N + 1)
                (B := fun _ => univ (ψ u1N)) (eqv_mem_univ a b')
                (fun _ _ => univ_mem_univ (ψ u1N))
            · simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
                eqReflA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
                eqReflA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
                eqReflA, ConstantInfo.toConstantVal]
              try rfl
            · rw [eqReflVal_app₂ hAmem hamem]
              exact pt_mem_eqv_self a
          · intro r Sr hSr hrmem
            simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
              eqReflA, ConstantInfo.toConstantVal,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSr
            subst hSr
            refine ⟨?_, ?_⟩
            · -- opened `∀ {b : α}, …`
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]), erB (ψ u1N), ?_⟩
              intro b Sb hSb hbmem
              simp [interpExpr, Expr.instantiate1, updV] at hSb
              subst hSb
              refine ⟨?_, ?_⟩
              · -- opened `∀ (t : Eq α a b), motive b t`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨?_, ψ u1N, ?_⟩
                · -- AnnotOk of `Eq α a b` (three app clauses)
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                      eqVal V ψ, A, Nat.max (ψ uN) (Nat.max (ψ uN) 1),
                      univ (ψ uN),
                      (fun X => pi (Nat.max (ψ uN) 1) X fun _ =>
                        pi 1 X fun _ => univ 0),
                      ?_, ?_, eqVal_mem, hAmem, fun X hX => eq_fibre_mem hX⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (eqVal V ψ) A, a, Nat.max (ψ uN) 1, A,
                      (fun _ => pi 1 A fun _ => univ 0),
                      ?_, ?_, eqVal_app_mem hAmem, hamem, fun y _ => ?_⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (SetTheory.app (eqVal V ψ) A) a, b, 1, A,
                      (fun _ => univ 0),
                      ?_, ?_, eqVal_app₂_mem hAmem hamem, hbmem,
                      fun y _ => univ_mem_univ 0⟩
                  · simp [interpExpr, Expr.instantiate1, updV, hfindE',
                      hvalE', eqA, ConstantInfo.toConstantVal]
                    try rfl
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV, hfindE',
                      hvalE', eqA, ConstantInfo.toConstantVal]
                    try rfl
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · exact pi_mem_univ (u := ψ uN) (v := 1)
                      (B := fun _ => univ 0) hAmem
                      (fun _ _ => univ_mem_univ 0)
                  · simp [interpExpr, Expr.instantiate1, updV, hfindE',
                      hvalE', eqA, ConstantInfo.toConstantVal]
                    try rfl
                  · simp [interpExpr, Expr.instantiate1, updV]
                · intro h Sh hSh hhmem
                  simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                    eqA, ConstantInfo.toConstantVal,
                    -ite_eq_left_iff, -ite_eq_right_iff,
                    -Nat.max_eq_zero_iff] at hSh
                  subst hSh
                  have hheqv : h ∈ˢ eqv a b := by
                    have : h ∈ˢ SetTheory.app (SetTheory.app
                        (SetTheory.app (eqVal V ψ) A) a) b := hhmem
                    rwa [eqVal_app₃ hAmem hamem hbmem] at this
                  refine ⟨?_, ?_⟩
                  · -- AnnotOk of the body `motive b t` (two app clauses)
                    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                    refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                        (by simp [Expr.instantiate1, AnnotOk]),
                        M, b, ψ u1N + 1, A,
                        (fun b' => pi (ψ u1N + 1) (eqv a b') fun _ =>
                          univ (ψ u1N)),
                        ?_, ?_, ?_, hbmem, ?_⟩,
                      (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app M b, h, ψ u1N + 1, eqv a b,
                      (fun _ => univ (ψ u1N)),
                      ?_, ?_, ?_, hheqv,
                      fun _ _ => univ_mem_univ (ψ u1N)⟩
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · have := hMmem'
                      simp only [eqRecMSpace] at this
                      exact this
                    · intro b' hb'
                      exact pi_mem_univ (u := 0) (v := ψ u1N + 1)
                        (B := fun _ => univ (ψ u1N)) (eqv_mem_univ a b')
                        (fun _ _ => univ_mem_univ (ψ u1N))
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · -- app M b at pi-level u1 (weakened annotation)
                      exact happM a hamem M hMmem' b hbmem
                  · -- fibre-universe of the `t` binder
                    refine ⟨SetTheory.app (SetTheory.app M b) h, ?_, ?_⟩
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · exact happ2M a hamem M hMmem' b hbmem h hheqv
              · -- fibre-universe of the `b` binder
                refine ⟨pi (ψ u1N)
                  (SetTheory.app (SetTheory.app
                    (SetTheory.app (eqVal V ψ) A) a) b)
                  (fun h' => SetTheory.app (SetTheory.app M b) h'), ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                    eqA, ConstantInfo.toConstantVal, Level.eval,
                    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                  try rfl
                · exact hT5 a hamem M hMmem' b hbmem
            · -- fibre-universe of the `refl` binder
              refine ⟨pi (erB (ψ u1N)) A (fun b' =>
                pi (ψ u1N)
                  (SetTheory.app (SetTheory.app
                    (SetTheory.app (eqVal V ψ) A) a) b')
                  (fun h' => SetTheory.app (SetTheory.app M b') h')), ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
                  eqA, ConstantInfo.toConstantVal, Level.eval,
                  -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                try rfl
              · exact hT4 a hamem M hMmem'
        · -- fibre-universe of the `motive` binder
          refine ⟨pi (erRefl (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            (fun _ => pi (erB (ψ u1N)) A fun b' =>
              pi (ψ u1N)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b')
                fun h' => SetTheory.app (SetTheory.app M b') h'), ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
              hfindR', hvalR', eqA, eqReflA, ConstantInfo.toConstantVal,
              Level.eval,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl
          · exact hT3 a hamem M hMmem'
    · -- fibre-universe of the `a` binder
      refine ⟨pi (erM (ψ uN) (ψ u1N))
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) (fun M' =>
        pi (erRefl (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M' a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          (fun _ => pi (erB (ψ u1N)) A fun b' =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) A) a) b')
              fun h' => SetTheory.app (SetTheory.app M' b') h')), ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
          hfindR', hvalR', eqA, eqReflA, ConstantInfo.toConstantVal,
          Level.eval,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
      · exact hT2 a hamem
  · -- fibre-universe of the `α` binder
    refine ⟨pi (erA (ψ uN) (ψ u1N)) A (fun a =>
      pi (erM (ψ uN) (ψ u1N))
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) (fun M' =>
        pi (erRefl (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M' a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          (fun _ => pi (erB (ψ u1N)) A fun b' =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) A) a) b')
              fun h' => SetTheory.app (SetTheory.app M' b') h'))), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
        hfindR', hvalR', eqA, eqReflA, ConstantInfo.toConstantVal,
        Level.eval,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · refine pi_mem_univ (u := ψ uN) (v := erA (ψ uN) (ψ u1N)) hAmem
        (fun a ha => ?_)
      rw [← erA₀_eq_erA]
      exact hT2 a ha

end Setlec
