import Setlec.Model.Basis.Util

/-!
# `PSigma'` basis block: interpretation and `hkey` obligations
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-! ## The `PSigma'` basis block -/

/-- Interpretation of `PSigma'`'s pinned type, computed. -/
theorem interp_psigma_type {cval : ConstVal V} :
    interpClosed V cval env ψ psigmaA.toConstantVal.type =
      some (pi
        (Nat.max (Nat.max (ψ uN) (ψ vN + 1)) (Nat.max (ψ uN) (ψ vN) + 1))
        (univ (ψ uN)) fun A =>
        pi (Nat.max (ψ uN) (ψ vN) + 1) (pi (ψ vN + 1) A fun _ => univ (ψ vN))
          fun _ => univ (Nat.max (ψ uN) (ψ vN))) := by
  simp only [interpClosed, psigmaA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD, reduceIte]
  simp [interpExpr, Expr.instantiate1, updV, uN, vN,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `PSigma'`'s value is a member of its pi-type. -/
theorem psigmaVal_mem :
    (psigmaVal V ψ : V) ∈ˢ pi
      (Nat.max (Nat.max (ψ uN) (ψ vN + 1)) (Nat.max (ψ uN) (ψ vN) + 1))
      (univ (ψ uN))
      (fun A => pi (Nat.max (ψ uN) (ψ vN) + 1)
        (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun _ =>
          univ (Nat.max (ψ uN) (ψ vN))) := by
  simp only [psigmaVal]
  refine lam_mem (V := V) (B := fun A => pi (Nat.max (ψ uN) (ψ vN) + 1)
    (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun _ =>
      univ (Nat.max (ψ uN) (ψ vN))) fun A hA => ?_
  refine lam_mem (V := V) (B := fun _ => univ (Nat.max (ψ uN) (ψ vN)))
    fun B hB => ?_
  exact sigma_mem_univ hA (fun x hx => app_mem hB hx fun _ _ =>
    univ_mem_univ (ψ vN))

/-- `PSigma'`'s value inhabits its type. -/
theorem psigma_key {cval : ConstVal V} :
    ∃ T, interpClosed V cval env ψ psigmaA.toConstantVal.type = some T ∧
      psigmaVal V ψ ∈ˢ T :=
  ⟨_, interp_psigma_type, psigmaVal_mem⟩

/-- `PSigma'`'s type carries truthful annotations. -/
theorem annotOk_psigma_type {cval : ConstVal V} :
    AnnotOk V cval env ψ 0 (rho0 V) psigmaA.toConstantVal.type := by
  simp only [psigmaA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · -- `∀ (β : α → Sort v), Sort (max u v)`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, ?_⟩
    · -- the binder type `(x : α) → Sort v`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, ?_⟩
      intro x Sx hSx hxmem
      refine ⟨trivial, ?_⟩
      refine ⟨univ (ψ vN), ?_⟩
      simp [interpExpr, Expr.instantiate1, updV, Level.eval, vN]
    · intro B SB hSB hBmem
      refine ⟨trivial, ?_⟩
      refine ⟨univ (Nat.max (ψ uN) (ψ vN)), ?_⟩
      simp [interpExpr, Expr.instantiate1, updV, Level.eval, uN, vN]
  · refine ⟨pi (Nat.max (ψ uN) (ψ vN) + 1)
      (pi (ψ vN + 1) A fun _ => univ (ψ vN)) (fun _ =>
        univ (Nat.max (ψ uN) (ψ vN))), ?_⟩
    simp [interpExpr, Expr.instantiate1, updV, Level.eval, uN, vN,
      -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
    try rfl


/-- Applying `PSigma'`'s value to a domain computes to the fibre-family
abstraction. -/
theorem psigmaVal_app {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (psigmaVal V ψ) A =
      SetTheory.lam (Nat.max (ψ uN) (ψ vN) + 1)
        (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
          sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B x := by
  simp only [psigmaVal]
  exact app_lam hA
    (B := fun X => pi (Nat.max (ψ uN) (ψ vN) + 1)
      (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun _ =>
        univ (Nat.max (ψ uN) (ψ vN)))
    (fun X hX => lam_mem (V := V)
      (B := fun _ => univ (Nat.max (ψ uN) (ψ vN)))
      fun B hB => sigma_mem_univ hX (fun x hx =>
        app_mem hB hx fun _ _ => univ_mem_univ (ψ vN)))
    (fun X hX => by
      have hdom : (pi (ψ vN + 1) X fun _ => univ (ψ vN)) ∈ˢ
          univ (Nat.max (ψ uN) (ψ vN + 1)) :=
        pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hX
          (fun _ _ => univ_mem_univ (ψ vN))
      exact pi_mem_univ (u := Nat.max (ψ uN) (ψ vN + 1))
        (v := Nat.max (ψ uN) (ψ vN) + 1) hdom
        (fun _ _ => univ_mem_univ (Nat.max (ψ uN) (ψ vN))))

theorem psigmaVal_app_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (psigmaVal V ψ) A ∈ˢ
      pi (Nat.max (ψ uN) (ψ vN) + 1) (pi (ψ vN + 1) A fun _ => univ (ψ vN))
        (fun _ => univ (Nat.max (ψ uN) (ψ vN))) := by
  rw [psigmaVal_app hA]
  exact lam_mem (V := V) (B := fun _ => univ (Nat.max (ψ uN) (ψ vN)))
    fun B hB => sigma_mem_univ hA (fun x hx =>
      app_mem hB hx fun _ _ => univ_mem_univ (ψ vN))

/-! Raw evaluations of `PSigma'.mk`'s binder annotations. -/

def emV (u v : Nat) : Nat :=
  if Nat.max u v = 0 then 0 else Nat.max v (Nat.max u v)
def emB (u v : Nat) : Nat :=
  if emV u v = 0 then 0 else Nat.max u (emV u v)
def emA (u v : Nat) : Nat :=
  if emB u v = 0 then 0 else Nat.max u (Nat.max (v + 1) (emB u v))



theorem emV_eq (u v : Nat) : emV u v = Nat.max u v := by
  unfold emV
  by_cases h : Nat.max u v = 0
  · rw [if_pos h, h]
  · rw [if_neg h]
    exact max_absorb_r' u v

theorem emB_eq (u v : Nat) : emB u v = Nat.max u v := by
  unfold emB
  rw [emV_eq]
  by_cases h : Nat.max u v = 0
  · rw [if_pos h, h]
  · rw [if_neg h]
    exact Nat.le_antisymm
      (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_refl _⟩)
      (Nat.le_max_right _ _)

theorem emA_eq (u v : Nat) :
    emA u v = if Nat.max u v = 0 then 0 else Nat.max u (v + 1) := by
  unfold emA
  rw [emB_eq]
  by_cases h : Nat.max u v = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact max_eqrec_a u v

/-- Interpretation of `PSigma'.mk`'s pinned type, computed. -/
theorem interp_psigmaMk_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    interpClosed V cval env ψ psigmaMkA.toConstantVal.type =
      some (pi (emA (ψ uN) (ψ vN)) (univ (ψ uN)) fun A =>
        pi (emB (ψ uN) (ψ vN)) (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
          pi (emV (ψ uN) (ψ vN)) A fun a =>
            pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a) fun _ =>
              SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B) := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  simp only [interpClosed, psigmaMkA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindS', hvalS', psigmaA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, vN,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `PSigma'.mk`'s value inhabits its type. -/
theorem psigmaMk_key {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    ∃ T, interpClosed V cval env ψ psigmaMkA.toConstantVal.type = some T ∧
      psigmaMkVal V ψ ∈ˢ T := by
  refine ⟨_, interp_psigmaMk_type hfindS hvalS, ?_⟩
  rw [emA_eq, emB_eq, emV_eq]
  simp only [psigmaMkVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun B hB => ?_
  refine lam_mem (V := V) fun a ha => ?_
  refine lam_mem (V := V) fun b hb => ?_
  rw [psigmaVal_fold hA hB]
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · simp only [hw, ↓reduceIte]
    exact pt_mem_sigma ha hb
  · simp only [if_neg hw]
    exact spair_mem hw ha hb


/-- `PSigma'.mk`'s type carries truthful annotations. -/
theorem annotOk_psigmaMk_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) psigmaMkA.toConstantVal.type := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  simp only [psigmaMkA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  -- the fibre-family space over `A`
  have hβmem : (pi (ψ vN + 1) A fun _ => univ (ψ vN)) ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN + 1)) :=
    pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hAmem
      (fun _ _ => univ_mem_univ (ψ vN))
  refine ⟨?_, ?_⟩
  · -- opened `∀ {β}, …`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, ?_⟩
    · -- the binder type `(x : α) → Sort v`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, ?_⟩
      intro x Sx hSx hxmem
      refine ⟨trivial, ?_⟩
      refine ⟨univ (ψ vN), ?_⟩
      simp [interpExpr, Expr.instantiate1, updV, Level.eval, vN]
    · intro B SB hSB hBmem
      simp [interpExpr, Expr.instantiate1, updV,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSB
      subst hSB
      have hBmem' : B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) := hBmem
      refine ⟨?_, ?_⟩
      · -- opened `∀ (fst : α), …`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
        intro a Sa hSa hamem
        simp [interpExpr, Expr.instantiate1, updV] at hSa
        subst hSa
        refine ⟨?_, ?_⟩
        · -- opened `∀ (snd : β fst), …`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
            (by simp [Expr.instantiate1, AnnotOk]), B, a, A,
            (fun _ => univ (ψ vN)), ?_, ?_, hBmem', hamem⟩, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV]
          · simp [interpExpr, Expr.instantiate1, updV]
          intro b Sb hSb hbmem
          simp [interpExpr, Expr.instantiate1, updV,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSb
          subst hSb
          refine ⟨?_, ?_⟩
          · -- the body `PSigma' α β` (two app clauses)
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                psigmaVal V ψ, A,
                univ (ψ uN),
                (fun X => pi (Nat.max (ψ uN) (ψ vN) + 1)
                  (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun _ =>
                    univ (Nat.max (ψ uN) (ψ vN))),
                ?_, ?_, psigmaVal_mem, hAmem⟩,
              (by simp [Expr.instantiate1, AnnotOk]),
              SetTheory.app (psigmaVal V ψ) A, B,
              pi (ψ vN + 1) A (fun _ => univ (ψ vN)),
              (fun _ => univ (Nat.max (ψ uN) (ψ vN))),
              ?_, ?_, psigmaVal_app_mem hAmem, hBmem'⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
                psigmaA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
                psigmaA, ConstantInfo.toConstantVal]
              try rfl
            · simp [interpExpr, Expr.instantiate1, updV]
          · -- fibre-universe of `snd` (annotation `max u v`)
            refine ⟨SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B, ?_⟩
            simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
              psigmaA, ConstantInfo.toConstantVal]
            try rfl
        · -- fibre-universe of `fst` (annotation `imax v (max u v)`)
          refine ⟨pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a)
            (fun _ => SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B),
            ?_⟩
          simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            psigmaA, ConstantInfo.toConstantVal, Level.eval,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
      · -- fibre-universe of `β`
        refine ⟨pi (emV (ψ uN) (ψ vN)) A (fun a =>
          pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a)
            (fun _ => SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)),
          ?_⟩
        simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
          psigmaA, ConstantInfo.toConstantVal, Level.eval,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
  · -- fibre-universe of `α`
    refine ⟨pi (emB (ψ uN) (ψ vN)) (pi (ψ vN + 1) A fun _ => univ (ψ vN))
      (fun B => pi (emV (ψ uN) (ψ vN)) A (fun a =>
        pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a)
          (fun _ => SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B))),
      ?_⟩
    simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
      psigmaA, ConstantInfo.toConstantVal, Level.eval,
      -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
    try rfl
/-! Membership forms for `PSigma'.mk`'s value and its partial
applications (the `AnnotOk` app clauses of the recursor's minor
premise). -/

theorem psigmaMk_space3 {A B' a' : V}
    (hA : A ∈ˢ univ (ψ uN)) (hB' : B' ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN))
    (ha' : a' ∈ˢ A) :
    (pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
      sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B' x) ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN)) := by
  have hBa : SetTheory.app B' a' ∈ˢ univ (ψ vN) :=
    app_mem hB' ha' fun _ _ => univ_mem_univ (ψ vN)
  have := pi_mem_univ (u := ψ vN) (v := Nat.max (ψ uN) (ψ vN)) hBa
    (fun _ _ => sigma_mem_univ hA fun x hx =>
      app_mem hB' hx fun _ _ => univ_mem_univ (ψ vN))
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · simpa [hw] using this
  · simpa [hw, max_absorb_r'] using this

theorem psigmaMk_space2 {A B' : V}
    (hA : A ∈ˢ univ (ψ uN)) (hB' : B' ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) :
    (pi (Nat.max (ψ uN) (ψ vN)) A fun a' =>
      pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
        sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B' x) ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN)) := by
  have := pi_mem_univ (u := ψ uN) (v := Nat.max (ψ uN) (ψ vN)) hA
    (fun a' ha' => psigmaMk_space3 hA hB' ha')
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · simpa [hw] using this
  · simpa [hw, max_absorb_l'] using this

theorem psigmaMk_space1 {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    (pi (Nat.max (ψ uN) (ψ vN)) (pi (ψ vN + 1) A fun _ => univ (ψ vN))
      fun B' => pi (Nat.max (ψ uN) (ψ vN)) A fun a' =>
        pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
          sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B' x) ∈ˢ
      univ (if Nat.max (ψ uN) (ψ vN) = 0 then 0
        else Nat.max (ψ uN) (ψ vN + 1)) := by
  have hdom : (pi (ψ vN + 1) A fun _ => univ (ψ vN)) ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN + 1)) :=
    pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hA
      (fun _ _ => univ_mem_univ (ψ vN))
  have := pi_mem_univ (u := Nat.max (ψ uN) (ψ vN + 1))
    (v := Nat.max (ψ uN) (ψ vN)) hdom
    (fun B' hB' => psigmaMk_space2 hA hB')
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · simpa [hw] using this
  · have habs : Nat.max (Nat.max (ψ uN) (ψ vN + 1)) (Nat.max (ψ uN) (ψ vN)) =
        Nat.max (ψ uN) (ψ vN + 1) :=
      Nat.le_antisymm
        (Nat.max_le.mpr ⟨Nat.le_refl _,
          Nat.max_le.mpr ⟨Nat.le_max_left _ _,
            Nat.le_trans (Nat.le_succ (ψ vN)) (Nat.le_max_right _ _)⟩⟩)
        (Nat.le_max_left _ _)
    simpa [hw, habs] using this

theorem psigmaMkVal_mem :
    (psigmaMkVal V ψ : V) ∈ˢ pi
      (if Nat.max (ψ uN) (ψ vN) = 0 then 0 else Nat.max (ψ uN) (ψ vN + 1))
      (univ (ψ uN))
      (fun X => pi (Nat.max (ψ uN) (ψ vN))
        (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun B' =>
          pi (Nat.max (ψ uN) (ψ vN)) X fun a' =>
            pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
              sigmaSet (Nat.max (ψ uN) (ψ vN)) X fun x =>
                SetTheory.app B' x) := by
  simp only [psigmaMkVal]
  refine lam_mem (V := V) fun X hX => ?_
  refine lam_mem (V := V) fun B' hB' => ?_
  refine lam_mem (V := V) fun a' ha' => ?_
  refine lam_mem (V := V) fun b hb => ?_
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · simp only [hw, ↓reduceIte]
    exact pt_mem_sigma ha' hb
  · simp only [if_neg hw]
    exact spair_mem hw ha' hb

theorem psigmaMkVal_app_mem {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (psigmaMkVal V ψ) A ∈ˢ
      pi (Nat.max (ψ uN) (ψ vN)) (pi (ψ vN + 1) A fun _ => univ (ψ vN))
        (fun B' => pi (Nat.max (ψ uN) (ψ vN)) A fun a' =>
          pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
            sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
              SetTheory.app B' x) :=
  app_mem psigmaMkVal_mem hA (fun _X hX => psigmaMk_space1 hX)

theorem psigmaMkVal_app₂_mem {A B : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) :
    SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B ∈ˢ
      pi (Nat.max (ψ uN) (ψ vN)) A (fun a' =>
        pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a') fun _ =>
          sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
            SetTheory.app B x) :=
  app_mem (psigmaMkVal_app_mem hA) hB
    (fun _B' hB' => psigmaMk_space2 hA hB')

theorem psigmaMkVal_app₃_mem {A B a : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B) a ∈ˢ
      pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a) (fun _ =>
        sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B x) :=
  app_mem (psigmaMkVal_app₂_mem hA hB) ha
    (fun _a' ha' => psigmaMk_space3 hA hB ha')

theorem psigmaMkVal_app₄_mem {A B a b : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) (ha : a ∈ˢ A)
    (hb : b ∈ˢ SetTheory.app B a) :
    SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (psigmaMkVal V ψ) A) B) a) b ∈ˢ
      sigmaSet (Nat.max (ψ uN) (ψ vN)) A (fun x => SetTheory.app B x) :=
  app_mem (psigmaMkVal_app₃_mem hA hB ha) hb
    (fun _ _ => sigma_mem_univ hA fun _x hx =>
      app_mem hB hx fun _ _ => univ_mem_univ (ψ vN))

/-- Interpretation of `PSigma'.rec`'s pinned type, computed (the whole
telescope is propositional: every binder annotation evaluates to `0`
definitionally). -/
theorem interp_psigmaRec_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ') :
    interpClosed V cval env ψ psigmaRecA.toConstantVal.type =
      some (pi 0 (univ (ψ uN)) fun A =>
        pi 0 (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
          pi 0 (pi 1
              (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
              fun _ => univ 0) fun M =>
            pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) fun _ =>
              pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
                fun t => SetTheory.app M t) := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  have hfindM' : env.find? ((Name.anonymous.str "PSigma'").str "mk") = some psigmaMkA :=
    hfindM
  have hvalM' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PSigma'").str "mk") ψ' = psigmaMkVal V ψ' := hvalM
  simp only [interpClosed, psigmaRecA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindS', hvalS', hfindM', hvalM', psigmaA, psigmaMkA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, vN,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `PSigma'.rec`'s value inhabits its type (elimination via
`mem_sigma_elim`: the target is the pair of its components — or the
proof point — so the minor premise's instance inhabits the motive's
fibre). -/
theorem psigmaRec_key {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ') :
    ∃ T, interpClosed V cval env ψ psigmaRecA.toConstantVal.type = some T ∧
      psigmaRecVal V ψ ∈ˢ T := by
  refine ⟨_, interp_psigmaRec_type hfindS hvalS hfindM hvalM, ?_⟩
  simp only [psigmaRecVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun B hB => ?_
  rw [psigmaVal_fold hA hB]
  refine lam_mem (V := V) fun M hM => ?_
  have hMin : (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
      SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) =
      (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (if Nat.max (ψ uN) (ψ vN) = 0 then pt
          else spair a b)) :=
    pi_congr fun a ha => pi_congr fun b hb => by
      rw [psigmaMkVal_fold hA hB ha hb]
  rw [hMin]
  refine lam_mem (V := V) fun m hm => ?_
  refine lam_mem (V := V) fun t ht => ?_
  obtain ⟨a', b', ha', hb', hw0, hwn⟩ := mem_sigma_elim ht
  have hMuniv : ∀ x, x ∈ˢ sigmaSet (Nat.max (ψ uN) (ψ vN)) A
      (fun x => SetTheory.app B x) → SetTheory.app M x ∈ˢ univ 0 :=
    fun x hx => app_mem hM hx (fun _ _ => univ_mem_univ 0)
  have hifmem : ∀ a, a ∈ˢ A → ∀ b, b ∈ˢ SetTheory.app B a →
      (if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a b) ∈ˢ
        sigmaSet (Nat.max (ψ uN) (ψ vN)) A (fun x => SetTheory.app B x) := by
    intro a ha b hb
    by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
    · simp only [hw, ↓reduceIte]
      exact pt_mem_sigma ha hb
    · simp only [if_neg hw]
      exact spair_mem hw ha hb
  have h1 : SetTheory.app m a' ∈ˢ pi 0 (SetTheory.app B a')
      (fun b => SetTheory.app M
        (if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a' b)) :=
    app_mem hm ha' (fun a ha => by
      have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
        app_mem hB ha fun _ _ => univ_mem_univ (ψ vN)
      exact pi_mem_univ (u := ψ vN) (v := 0) hBa
        (fun b hb => hMuniv _ (hifmem a ha b hb)))
  have h2 : SetTheory.app (SetTheory.app m a') b' ∈ˢ
      SetTheory.app M (if Nat.max (ψ uN) (ψ vN) = 0 then pt
        else spair a' b') :=
    app_mem h1 hb' (fun b hb => hMuniv _ (hifmem a' ha' b hb))
  have hteq : (if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a' b') = t := by
    by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
    · rw [if_pos hw, hw0 hw]
    · rw [if_neg hw, hwn hw]
  rw [hteq] at h2
  have hpt : SetTheory.app (SetTheory.app m a') b' = pt :=
    mem_univ_zero (hMuniv t ht) h2
  rw [← hpt]
  exact h2


/-- `PSigma'.rec`'s type carries truthful annotations. -/
theorem annotOk_psigmaRec_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) psigmaRecA.toConstantVal.type := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  have hfindM' : env.find? ((Name.anonymous.str "PSigma'").str "mk") = some psigmaMkA :=
    hfindM
  have hvalM' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PSigma'").str "mk") ψ' = psigmaMkVal V ψ' := hvalM
  simp only [psigmaRecA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  -- shared facts over `A`
  have hsigU : ∀ B, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B ∈ˢ
        univ (Nat.max (ψ uN) (ψ vN)) := by
    intro B hB
    rw [psigmaVal_fold hAmem hB]
    exact sigma_mem_univ hAmem (fun x hx =>
      app_mem hB hx fun _ _ => univ_mem_univ (ψ vN))
  -- the two-app `PSigma' α β` AnnotOk clause, for a given fibre value
  have hPSclause : ∀ (d' : Nat) (ρ' : Nat → V) (f a' : Expr),
      interpExpr V cval env ψ d' ρ' f = some (psigmaVal V ψ) →
      True := fun _ _ _ _ _ => trivial
  clear hPSclause
  refine ⟨?_, ?_⟩
  · -- opened `∀ {β}, …`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, ?_⟩
    · -- the binder type `(x : α) → Sort v`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, ?_⟩
      intro x Sx hSx hxmem
      refine ⟨trivial, ?_⟩
      refine ⟨univ (ψ vN), ?_⟩
      simp [interpExpr, Expr.instantiate1, updV, Level.eval, vN]
    · intro B SB hSB hBmem
      simp [interpExpr, Expr.instantiate1, updV,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSB
      subst hSB
      have hBmem' : B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) := hBmem
      refine ⟨?_, ?_⟩
      · -- opened `∀ {motive}, …`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨?_, ?_⟩
        · -- the motive space `(t : PSigma' α β) → Prop`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
              psigmaVal V ψ, A,
              univ (ψ uN),
              (fun X => pi (Nat.max (ψ uN) (ψ vN) + 1)
                (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun _ =>
                  univ (Nat.max (ψ uN) (ψ vN))),
              ?_, ?_, psigmaVal_mem, hAmem⟩,
            (by simp [Expr.instantiate1, AnnotOk]),
            SetTheory.app (psigmaVal V ψ) A, B,
            pi (ψ vN + 1) A (fun _ => univ (ψ vN)),
            (fun _ => univ (Nat.max (ψ uN) (ψ vN))),
            ?_, ?_, psigmaVal_app_mem hAmem, hBmem'⟩, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
              psigmaA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
          · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
              psigmaA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
          · intro t St hSt htmem
            refine ⟨trivial, ?_⟩
            refine ⟨univ 0, ?_⟩
            simp [interpExpr, Expr.instantiate1, updV, Level.eval]
        · intro M SM hSM hMmem
          simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            psigmaA, ConstantInfo.toConstantVal, Level.eval,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSM
          subst hSM
          have hMmem' : M ∈ˢ pi 1
              (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
              (fun _ => univ 0) := hMmem
          have happM : ∀ x, x ∈ˢ
              SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B →
              SetTheory.app M x ∈ˢ univ 0 :=
            fun x hx => app_mem hMmem' hx (fun _ _ => univ_mem_univ 0)
          have hmk4 : ∀ a, a ∈ˢ A → ∀ b, b ∈ˢ SetTheory.app B a →
              SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
                (psigmaMkVal V ψ) A) B) a) b ∈ˢ
              SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B := by
            intro a ha b hb
            rw [psigmaVal_fold hAmem hBmem']
            exact psigmaMkVal_app₄_mem hAmem hBmem' ha hb
          refine ⟨?_, ?_⟩
          · -- opened `∀ (mk : …), …`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨?_, ?_⟩
            · -- the minor-premise space
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
              intro a Sa hSa hamem
              simp [interpExpr, Expr.instantiate1, updV] at hSa
              subst hSa
              refine ⟨?_, ?_⟩
              · -- opened `∀ (snd : β fst), motive (mk …)`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                  (by simp [Expr.instantiate1, AnnotOk]), B, a, A,
                  (fun _ => univ (ψ vN)), ?_, ?_, hBmem', hamem⟩, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV]
                · simp [interpExpr, Expr.instantiate1, updV]
                intro b Sb hSb hbmem
                simp [interpExpr, Expr.instantiate1, updV,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff] at hSb
                subst hSb
                refine ⟨?_, ?_⟩
                · -- the body `motive (mk α β fst snd)`
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                    ⟨⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                      psigmaMkVal V ψ, A,
                      univ (ψ uN),
                      (fun X => pi (Nat.max (ψ uN) (ψ vN))
                        (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun B' =>
                          pi (Nat.max (ψ uN) (ψ vN)) X fun a' =>
                            pi (Nat.max (ψ uN) (ψ vN))
                              (SetTheory.app B' a') fun _ =>
                              sigmaSet (Nat.max (ψ uN) (ψ vN)) X fun x =>
                                SetTheory.app B' x),
                      ?_, ?_, psigmaMkVal_mem, hAmem⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (psigmaMkVal V ψ) A, B,
                      pi (ψ vN + 1) A (fun _ => univ (ψ vN)),
                      (fun B' => pi (Nat.max (ψ uN) (ψ vN)) A fun a' =>
                        pi (Nat.max (ψ uN) (ψ vN))
                          (SetTheory.app B' a') fun _ =>
                          sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
                            SetTheory.app B' x),
                      ?_, ?_, psigmaMkVal_app_mem hAmem, hBmem'⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B,
                      a, A,
                      (fun a' => pi (Nat.max (ψ uN) (ψ vN))
                        (SetTheory.app B a') fun _ =>
                        sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
                          SetTheory.app B x),
                      ?_, ?_, psigmaMkVal_app₂_mem hAmem hBmem', hamem⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (SetTheory.app (SetTheory.app
                        (psigmaMkVal V ψ) A) B) a,
                      b, SetTheory.app B a,
                      (fun _ => sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
                        SetTheory.app B x),
                      ?_, ?_, psigmaMkVal_app₃_mem hAmem hBmem' hamem, hbmem⟩,
                    M,
                    SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
                      (psigmaMkVal V ψ) A) B) a) b,
                    SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B,
                    (fun _ => univ 0),
                    ?_, ?_, hMmem', hmk4 a hamem b hbmem⟩
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                · -- fibre-universe of `snd` (annotation `0`)
                  refine ⟨SetTheory.app M (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                      a) b), ?_⟩
                  simp [interpExpr, Expr.instantiate1, updV, hfindM',
                    hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                  try rfl
              · -- fibre-universe of `fst` (annotation `imax v 0`)
                refine ⟨pi 0 (SetTheory.app B a) (fun b =>
                  SetTheory.app M (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                      a) b)), ?_⟩
                simp [interpExpr, Expr.instantiate1, updV, hfindM',
                  hvalM', psigmaMkA, ConstantInfo.toConstantVal, Level.eval,
                  -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                try rfl
            · intro m Sm hSm hmmem
              simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
                hfindM', hvalM', psigmaA, psigmaMkA,
                ConstantInfo.toConstantVal, Level.eval,
                -ite_eq_left_iff, -ite_eq_right_iff,
                -Nat.max_eq_zero_iff] at hSm
              subst hSm
              refine ⟨?_, ?_⟩
              · -- opened `∀ (t : PSigma' α β), motive t`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                    psigmaVal V ψ, A,
                    univ (ψ uN),
                    (fun X => pi (Nat.max (ψ uN) (ψ vN) + 1)
                      (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun _ =>
                        univ (Nat.max (ψ uN) (ψ vN))),
                    ?_, ?_, psigmaVal_mem, hAmem⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                  SetTheory.app (psigmaVal V ψ) A, B,
                  pi (ψ vN + 1) A (fun _ => univ (ψ vN)),
                  (fun _ => univ (Nat.max (ψ uN) (ψ vN))),
                  ?_, ?_, psigmaVal_app_mem hAmem, hBmem'⟩, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV, hfindS',
                    hvalS', psigmaA, ConstantInfo.toConstantVal]
                  try rfl
                · simp [interpExpr, Expr.instantiate1, updV]
                · simp [interpExpr, Expr.instantiate1, updV, hfindS',
                    hvalS', psigmaA, ConstantInfo.toConstantVal]
                  try rfl
                · simp [interpExpr, Expr.instantiate1, updV]
                intro t St hSt htmem
                simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
                  psigmaA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff] at hSt
                subst hSt
                refine ⟨?_, ?_⟩
                · -- the body `motive t`
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                    (by simp [Expr.instantiate1, AnnotOk]),
                    M, t,
                    SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B,
                    (fun _ => univ 0),
                    ?_, ?_, hMmem', htmem⟩
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV]
                · -- fibre-universe of `t` (annotation `0`)
                  refine ⟨SetTheory.app M t, ?_⟩
                  simp [interpExpr, Expr.instantiate1, updV]
              · -- fibre-universe of `mk` (annotation `imax (max u v) 0`)
                refine ⟨pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
                  (fun t => SetTheory.app M t), ?_⟩
                simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
                  psigmaA, ConstantInfo.toConstantVal, Level.eval,
                  -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                try rfl
          · -- fibre-universe of `motive`
            refine ⟨pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
              (fun _ => pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
                (fun t => SetTheory.app M t)), ?_⟩
            simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
              hfindM', hvalM', psigmaA, psigmaMkA,
              ConstantInfo.toConstantVal, Level.eval,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl
      · -- fibre-universe of `β`
        refine ⟨pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
          (fun _ => univ 0)) (fun M =>
            pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
              (fun _ => pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
                (fun t => SetTheory.app M t))), ?_⟩
        simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
          hfindM', hvalM', psigmaA, psigmaMkA,
          ConstantInfo.toConstantVal, Level.eval,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
  · -- fibre-universe of `α`
    refine ⟨pi 0 (pi (ψ vN + 1) A fun _ => univ (ψ vN)) (fun B =>
      pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        (fun _ => univ 0)) (fun M =>
          pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
            (fun _ => pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
              (fun t => SetTheory.app M t)))), ?_⟩
    simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
      hfindM', hvalM', psigmaA, psigmaMkA,
      ConstantInfo.toConstantVal, Level.eval,
      -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
    try rfl
/-! Partial-application computations for `PSigma'.mk`'s value (the
`PairMkFacts` domain facts read the `lam` tags off these). -/

theorem psigmaMkVal_app {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (psigmaMkVal V ψ) A =
      SetTheory.lam (Nat.max (ψ uN) (ψ vN))
        (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
        SetTheory.lam (Nat.max (ψ uN) (ψ vN)) A fun a =>
          SetTheory.lam (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a) fun b =>
            if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a b := by
  simp only [psigmaMkVal]
  exact app_lam hA
    (B := fun X => pi (Nat.max (ψ uN) (ψ vN))
      (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun B' =>
        pi (Nat.max (ψ uN) (ψ vN)) X fun a' =>
          pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
            sigmaSet (Nat.max (ψ uN) (ψ vN)) X fun x => SetTheory.app B' x)
    (fun _X hX => lam_mem (V := V) fun _B' hB' =>
      lam_mem (V := V) fun _a' ha' => lam_mem (V := V) fun _b hb => by
        by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
        · simp only [hw, ↓reduceIte]
          exact pt_mem_sigma ha' hb
        · simp only [if_neg hw]
          exact spair_mem hw ha' hb)
    (fun _X hX => psigmaMk_space1 hX)

theorem psigmaMkVal_app₂ {A B : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) :
    SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B =
      SetTheory.lam (Nat.max (ψ uN) (ψ vN)) A fun a =>
        SetTheory.lam (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a) fun b =>
          if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a b := by
  rw [psigmaMkVal_app hA]
  exact app_lam hB
    (B := fun B' => pi (Nat.max (ψ uN) (ψ vN)) A fun a' =>
      pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B' a') fun _ =>
        sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B' x)
    (fun _B' hB' => lam_mem (V := V) fun _a' ha' =>
      lam_mem (V := V) fun _b hb => by
        by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
        · simp only [hw, ↓reduceIte]
          exact pt_mem_sigma ha' hb
        · simp only [if_neg hw]
          exact spair_mem hw ha' hb)
    (fun _B' hB' => psigmaMk_space2 hA hB')

theorem psigmaMkVal_app₃ {A B a : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B) a =
      SetTheory.lam (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a) fun b =>
        if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair a b := by
  rw [psigmaMkVal_app₂ hA hB]
  exact app_lam ha
    (B := fun a' => pi (Nat.max (ψ uN) (ψ vN)) (SetTheory.app B a') fun _ =>
      sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x => SetTheory.app B x)
    (fun _a' ha' => lam_mem (V := V) fun _b hb => by
      by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
      · simp only [hw, ↓reduceIte]
        exact pt_mem_sigma ha' hb
      · simp only [if_neg hw]
        exact spair_mem hw ha' hb)
    (fun _a' ha' => psigmaMk_space3 hA hB ha')


/-! ## The pair projection-table entries -/

/-- Interpretation of the first pair entry's pinned type, computed. -/
theorem interp_pairFst_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    interpClosed V cval env ψ pairFstA.toConstantVal.type =
      some (pi (if (if ψ uN = 0 then 0
            else Nat.max (Nat.max (ψ uN) (ψ vN)) (ψ uN)) = 0 then 0
          else Nat.max (Nat.max (ψ uN) (ψ vN + 1))
            (if ψ uN = 0 then 0
              else Nat.max (Nat.max (ψ uN) (ψ vN)) (ψ uN)))
        (univ (ψ uN)) fun A =>
        pi (if ψ uN = 0 then 0
            else Nat.max (Nat.max (ψ uN) (ψ vN)) (ψ uN))
          (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
          pi (ψ uN)
            (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            fun _t => A) := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  simp only [interpClosed, pairFstA, pairFstEntry, ConstantInfo.toConstantVal,
    pairFstTyA, interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindS', hvalS', psigmaA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, vN,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- Interpretation of the second pair entry's pinned type, computed. -/
theorem interp_pairSnd_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    interpClosed V cval env ψ pairSndA.toConstantVal.type =
      some (pi (if (if ψ vN = 0 then 0
            else Nat.max (Nat.max (ψ uN) (ψ vN)) (ψ vN)) = 0 then 0
          else Nat.max (Nat.max (ψ uN) (ψ vN + 1))
            (if ψ vN = 0 then 0
              else Nat.max (Nat.max (ψ uN) (ψ vN)) (ψ vN)))
        (univ (ψ uN)) fun A =>
        pi (if ψ vN = 0 then 0
            else Nat.max (Nat.max (ψ uN) (ψ vN)) (ψ vN))
          (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
          pi (ψ vN)
            (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            fun t => SetTheory.app B (sfst t)) := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  simp only [interpClosed, pairSndA, pairSndEntry, ConstantInfo.toConstantVal,
    pairSndTyA, interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindS', hvalS', psigmaA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, vN,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- The first pair entry's value inhabits its pinned type. -/
theorem pairFst_key {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    ∃ T, interpClosed V cval env ψ pairFstA.toConstantVal.type = some T ∧
      pairFstVal V ψ ∈ˢ T := by
  refine ⟨_, interp_pairFst_type hfindS hvalS, ?_⟩
  simp only [pairFstVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun B hB => ?_
  rw [psigmaVal_fold hA hB]
  refine lam_mem (V := V) fun t ht => ?_
  obtain ⟨a', b', ha', hb', hw0, hwn⟩ := mem_sigma_elim ht
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · rw [hw0 hw, sfst_pt]
    have hu0 : ψ uN = 0 :=
      Nat.le_zero.mp (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hw))
    have hA0 : A ∈ˢ univ 0 := hu0 ▸ hA
    exact (mem_univ_zero hA0 ha') ▸ ha'
  · rw [hwn hw, sfst_spair]
    exact ha'

/-- The second pair entry's value inhabits its pinned type. -/
theorem pairSnd_key {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    ∃ T, interpClosed V cval env ψ pairSndA.toConstantVal.type = some T ∧
      pairSndVal V ψ ∈ˢ T := by
  refine ⟨_, interp_pairSnd_type hfindS hvalS, ?_⟩
  simp only [pairSndVal]
  refine lam_mem (V := V) fun A hA => ?_
  refine lam_mem (V := V) fun B hB => ?_
  rw [psigmaVal_fold hA hB]
  refine lam_mem (V := V) fun t ht => ?_
  obtain ⟨a', b', ha', hb', hw0, hwn⟩ := mem_sigma_elim ht
  by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
  · rw [hw0 hw, ssnd_pt, sfst_pt]
    have hu0 : ψ uN = 0 :=
      Nat.le_zero.mp (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hw))
    have hv0 : ψ vN = 0 :=
      Nat.le_zero.mp (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hw))
    have hA0 : A ∈ˢ univ 0 := hu0 ▸ hA
    have hapt : a' = pt := mem_univ_zero hA0 ha'
    have hb'' : b' ∈ˢ SetTheory.app B pt := hapt ▸ hb'
    have hB0 : SetTheory.app B pt ∈ˢ univ 0 := by
      have := app_mem hB (hapt ▸ ha') fun _ _ => univ_mem_univ (ψ vN)
      exact hv0 ▸ this
    exact (mem_univ_zero hB0 hb'') ▸ hb''
  · rw [hwn hw, ssnd_spair, sfst_spair]
    exact hb'


/-- The first pair entry's pinned type carries truthful annotations. -/
theorem annotOk_pairFst_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) pairFstA.toConstantVal.type := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  simp only [pairFstA, pairFstEntry, ConstantInfo.toConstantVal,
    pairFstTyA, AnnotOk]
  refine ⟨trivial, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · -- opened `∀ {β}, ∀ (t : PSigma' α β), α`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, ?_⟩
    · -- the binder type `(x : α) → Sort v`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, ?_⟩
      intro x Sx hSx hxmem
      refine ⟨trivial, ?_⟩
      refine ⟨univ (ψ vN), ?_⟩
      simp [interpExpr, Expr.instantiate1, updV, Level.eval, vN]
    · intro B SB hSB hBmem
      simp [interpExpr, Expr.instantiate1, updV,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSB
      subst hSB
      have hBmem' : B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) := hBmem
      refine ⟨?_, ?_⟩
      · -- opened `∀ (t : PSigma' α β), α`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
            psigmaVal V ψ, A,
            univ (ψ uN),
            (fun X => pi (Nat.max (ψ uN) (ψ vN) + 1)
              (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun _ =>
                univ (Nat.max (ψ uN) (ψ vN))),
            ?_, ?_, psigmaVal_mem, hAmem⟩,
          (by simp [Expr.instantiate1, AnnotOk]),
          SetTheory.app (psigmaVal V ψ) A, B,
          pi (ψ vN + 1) A (fun _ => univ (ψ vN)),
          (fun _ => univ (Nat.max (ψ uN) (ψ vN))),
          ?_, ?_, psigmaVal_app_mem hAmem, hBmem'⟩, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            psigmaA, ConstantInfo.toConstantVal]
          try rfl
        · simp [interpExpr, Expr.instantiate1, updV]
        · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            psigmaA, ConstantInfo.toConstantVal]
          try rfl
        · simp [interpExpr, Expr.instantiate1, updV]
        · intro t St hSt htmem
          refine ⟨trivial, ?_⟩
          refine ⟨A, ?_⟩
          simp [interpExpr, Expr.instantiate1, updV]
      · -- fibre of the β binder
        refine ⟨pi (ψ uN)
            (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            (fun _t => A), ?_⟩
        try simp only [Expr.instantiate1, reduceIte]
        simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
          psigmaA, ConstantInfo.toConstantVal, Level.eval, uN, vN,
          Level.substFn,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
  · -- fibre of the α binder
    refine ⟨pi (if ψ uN = 0 then 0
        else Nat.max (Nat.max (ψ uN) (ψ vN)) (ψ uN))
        (pi (ψ vN + 1) A fun _ => univ (ψ vN)) (fun B =>
          pi (ψ uN) (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            fun _t => A), ?_⟩
    try simp only [Expr.instantiate1, reduceIte]
    simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
      psigmaA, ConstantInfo.toConstantVal, uN, vN, Level.eval,
      Level.substFn,
      -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
    try rfl
/-- The second pair entry's pinned type carries truthful
annotations. -/
theorem annotOk_pairSnd_type {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) pairSndA.toConstantVal.type := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  simp only [pairSndA, pairSndEntry, ConstantInfo.toConstantVal,
    pairSndTyA, AnnotOk]
  refine ⟨trivial, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  refine ⟨?_, ?_⟩
  · -- opened `∀ {β}, ∀ (t : PSigma' α β), β t.0`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, ?_⟩
    · -- the binder type `(x : α) → Sort v`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, ?_⟩
      intro x Sx hSx hxmem
      refine ⟨trivial, ?_⟩
      refine ⟨univ (ψ vN), ?_⟩
      simp [interpExpr, Expr.instantiate1, updV, Level.eval, vN]
    · intro B SB hSB hBmem
      simp [interpExpr, Expr.instantiate1, updV,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSB
      subst hSB
      have hBmem' : B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) := hBmem
      have hfibB : ∀ x, x ∈ˢ A → SetTheory.app B x ∈ˢ univ (ψ vN) :=
        fun x hx => app_mem hBmem' hx fun _ _ => univ_mem_univ (ψ vN)
      have hsf : ∀ t, t ∈ˢ sigmaSet (Nat.max (ψ uN) (ψ vN)) A
          (fun x => SetTheory.app B x) → sfst t ∈ˢ A := by
        intro t ht
        obtain ⟨a', b', ha', hb', hw0, hwn⟩ := mem_sigma_elim ht
        by_cases hw : Nat.max (ψ uN) (ψ vN) = 0
        · rw [hw0 hw, sfst_pt]
          have hu0 : ψ uN = 0 := Nat.le_zero.mp
            (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hw))
          exact (mem_univ_zero (hu0 ▸ hAmem) ha') ▸ ha'
        · rw [hwn hw, sfst_spair]
          exact ha'
      refine ⟨?_, ?_⟩
      · -- opened `∀ (t : PSigma' α β), β t.0`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
            psigmaVal V ψ, A,
            univ (ψ uN),
            (fun X => pi (Nat.max (ψ uN) (ψ vN) + 1)
              (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun _ =>
                univ (Nat.max (ψ uN) (ψ vN))),
            ?_, ?_, psigmaVal_mem, hAmem⟩,
          (by simp [Expr.instantiate1, AnnotOk]),
          SetTheory.app (psigmaVal V ψ) A, B,
          pi (ψ vN + 1) A (fun _ => univ (ψ vN)),
          (fun _ => univ (Nat.max (ψ uN) (ψ vN))),
          ?_, ?_, psigmaVal_app_mem hAmem, hBmem'⟩, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            psigmaA, ConstantInfo.toConstantVal]
          try rfl
        · simp [interpExpr, Expr.instantiate1, updV]
        · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            psigmaA, ConstantInfo.toConstantVal]
          try rfl
        · simp [interpExpr, Expr.instantiate1, updV]
        · intro t St hSt htmem
          simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            psigmaA, ConstantInfo.toConstantVal,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            at hSt
          subst hSt
          have hψid : Level.substFn ψ
              [Name.anonymous.str "u", Name.anonymous.str "v"]
              [Level.param (Name.anonymous.str "u"),
               Level.param (Name.anonymous.str "v")] = ψ :=
            funext fun p => Level.substFn_map_param
              (ks := [Name.anonymous.str "u", Name.anonymous.str "v"])
          rw [hψid] at htmem
          rw [psigmaVal_fold hAmem hBmem'] at htmem
          refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
            ⟨(by simp [Expr.instantiate1, AnnotOk]), by omega, t, ψ uN,
              ψ vN, A,
              (fun x => SetTheory.app B x),
              (by simp [interpExpr, Expr.instantiate1, updV]), htmem,
              hAmem, hfibB⟩,
            B, sfst t, A, (fun _ => univ (ψ vN)),
            (by simp [interpExpr, Expr.instantiate1, updV]),
            (by simp [interpExpr, Expr.instantiate1, updV]),
            hBmem', hsf t htmem⟩, ?_⟩
          refine ⟨SetTheory.app B (sfst t), ?_⟩
          simp [interpExpr, Expr.instantiate1, updV]
      · -- fibre of the β binder
        refine ⟨pi (ψ vN)
            (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            (fun t => SetTheory.app B (sfst t)), ?_⟩
        try simp only [Expr.instantiate1, reduceIte]
        simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
          psigmaA, ConstantInfo.toConstantVal, Level.eval, uN, vN,
          Level.substFn,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
  · -- fibre of the α binder
    refine ⟨pi (if ψ vN = 0 then 0
        else Nat.max (Nat.max (ψ uN) (ψ vN)) (ψ vN))
        (pi (ψ vN + 1) A fun _ => univ (ψ vN)) (fun B =>
          pi (ψ vN) (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            fun t => SetTheory.app B (sfst t)), ?_⟩
    try simp only [Expr.instantiate1, reduceIte]
    simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
      psigmaA, ConstantInfo.toConstantVal, uN, vN, Level.eval,
      Level.substFn,
      -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
    try rfl
end Setlec
