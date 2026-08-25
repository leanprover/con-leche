import Setlec.Model.BasisInstall

/-!
# `Eq.rec` iota-rule semantics
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-- The (annotated) rhs of `Eq.rec`'s single rule. -/
def eqRecRhsA : Expr := ((ConstantInfo.recRules eqRecA).getD 0 default).rhs

/-! The rhs's own lam-tag evaluations. -/

def eqRhsA' (u u1 : Nat) : Nat :=
  if erB u1 = 0 then 0 else Nat.max u (Nat.max (u1 + 1) (erB u1))
def eqRhsAl' (u u1 : Nat) : Nat :=
  if eqRhsA' u u1 = 0 then 0 else Nat.max u (eqRhsA' u u1)

theorem eqRhsA'_eq (u u1 : Nat) :
    eqRhsA' u u1 = if u1 = 0 then 0 else Nat.max u (u1 + 1) := by
  unfold eqRhsA'
  rw [erB_eq]
  by_cases h : u1 = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact max_eqrec_a'' u u1

theorem eqRhsAl'_eq (u u1 : Nat) :
    eqRhsAl' u u1 = if u1 = 0 then 0 else Nat.max u (u1 + 1) := by
  unfold eqRhsAl'
  rw [eqRhsA'_eq]
  by_cases h : u1 = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_r' (Nat.succ_ne_zero u1))]
    exact max_absorb_l' u (u1 + 1)

/-- Interpretation of the `Eq.rec` rule rhs. -/
theorem interp_eqRec_rhs {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ') :
    interpClosed V cval env ψ eqRecRhsA =
      some (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
        SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r) := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindR' : env.find? ((Name.anonymous.str "Eq").str "refl") = some eqReflA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "refl") ψ' = eqReflVal V ψ' := hvalR
  simp only [interpClosed, eqRecRhsA, eqRecA, ConstantInfo.recRules,
    List.getD, List.getElem?_cons_zero, Option.getD_some,
    interpExpr, Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindE', hvalE', hfindR', hvalR', eqA, eqReflA, List.length_cons,
    List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN, u1N,
    hfindE', hvalE', hfindR', hvalR', eqA, eqReflA,
    ConstantInfo.toConstantVal,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl


/-- The `Eq.rec` rule rhs carries truthful annotations. -/
theorem annotOk_eqRec_rhs {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) eqRecRhsA := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindR' : env.find? ((Name.anonymous.str "Eq").str "refl") = some eqReflA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "refl") ψ' = eqReflVal V ψ' := hvalR
  simp only [eqRecRhsA, eqRecA, ConstantInfo.recRules, List.getD,
    List.getElem?_cons_zero, Option.getD_some, AnnotOk]
  refine ⟨trivial,
    (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N + 1)), ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  have hMSmem : ∀ a', a' ∈ˢ A →
      eqRecMSpace V (ψ u1N) A a' ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
    intro a' ha'
    unfold eqRecMSpace
    exact pi_mem_univ (u := ψ uN) (v := ψ u1N + 1) hAmem
      (fun b hb => pi_mem_univ (u := 0) (v := ψ u1N + 1)
        (B := fun _ => univ (ψ u1N))
        (eqv_mem_univ a' b) (fun _ _ => univ_mem_univ (ψ u1N)))
  have hMSeq : ∀ a', a' ∈ˢ A →
      (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a' := by
    intro a' ha'
    unfold eqRecMSpace
    exact pi_congr fun b hb => by rw [eqVal_app₃ hAmem ha' hb]
  have happM : ∀ a', a' ∈ˢ A → ∀ M', M' ∈ˢ eqRecMSpace V (ψ u1N) A a' →
      SetTheory.app (SetTheory.app M' a')
        (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a') ∈ˢ
        univ (ψ u1N) := by
    intro a' ha' M' hM'
    rw [eqReflVal_app₂ hAmem ha']
    have hMa : SetTheory.app M' a' ∈ˢ pi (ψ u1N + 1) (eqv a' a')
        (fun _ => univ (ψ u1N)) := by
      have hM'' := hM'
      simp only [eqRecMSpace] at hM''
      exact app_mem hM'' ha' (fun b hb =>
        pi_mem_univ (u := 0) (v := ψ u1N + 1) (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a' b) (fun _ _ => univ_mem_univ (ψ u1N)))
    exact app_mem hMa (pt_mem_eqv_self a') (fun _ _ => univ_mem_univ (ψ u1N))
  refine ⟨?_, ?_⟩
  · -- opened `λ (a : α), …`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨trivial,
      (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N + 1)), ?_⟩
    intro a Sa hSa hamem
    simp only [interpExpr, Expr.instantiate1, reduceIte, updV,
      Option.some.injEq] at hSa
    subst hSa
    refine ⟨?_, ?_⟩
    · -- opened `λ (motive : …), …`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨?_,
        (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N)), ?_⟩
      · -- the motive space type (as in the recursor's type)
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
          Nat.max 0 (ψ u1N + 1), ?_⟩
        refine ⟨?_, ?_⟩
        · first
            | (rintro v ⟨rfl⟩; exact fun z hz => hz)
            | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
            | (rintro v ⟨rfl⟩
               intro z hz
               refine univ_mono ?_ z hz
               simp only [Level.eval, u1N, uN]
               by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "u_1") = 0 <;> simp [h1, h2] <;> omega)
        intro b Sb hSb hbmem
        simp [interpExpr, Expr.instantiate1, updV] at hSb
        subst hSb
        refine ⟨?_, ?_⟩
        · try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨?_, ψ u1N + 1, ?_⟩
          · try simp only [Expr.instantiate1, reduceIte, AnnotOk]
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
          · refine ⟨?_, ?_⟩
            · first
                | (rintro v ⟨rfl⟩; exact fun z hz => hz)
                | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
                | (rintro v ⟨rfl⟩
                   intro z hz
                   refine univ_mono ?_ z hz
                   simp only [Level.eval, u1N, uN]
                   by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "u_1") = 0 <;> simp [h1, h2] <;> omega)
            intro h Sh hSh hhmem
            refine ⟨trivial, ?_⟩
            refine ⟨univ (ψ u1N), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, Level.eval, u1N]
            · exact univ_mem_univ (ψ u1N)
        · refine ⟨pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            (fun _ => univ (ψ u1N)), ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
              eqA, ConstantInfo.toConstantVal, Level.eval, u1N,
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
        · -- opened `λ (refl : motive a (Eq.refl α a)). refl`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨?_, ψ u1N, ?_⟩
          · -- the refl-domain annotations (as in the recursor's type)
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
              ?_, ?_, ?_, ?_,
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
            · have hMa : SetTheory.app M a ∈ˢ pi (ψ u1N + 1) (eqv a a)
                  (fun _ => univ (ψ u1N)) := by
                have hM'' := hMmem'
                simp only [eqRecMSpace] at hM''
                exact app_mem hM'' hamem (fun b hb =>
                  pi_mem_univ (u := 0) (v := ψ u1N + 1)
                    (B := fun _ => univ (ψ u1N)) (eqv_mem_univ a b)
                    (fun _ _ => univ_mem_univ (ψ u1N)))
              exact hMa
            · rw [eqReflVal_app₂ hAmem hamem]
              exact pt_mem_eqv_self a
          · intro r Sr hSr hrmem
            refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
            refine ⟨r, SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a),
              ?_, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
                eqReflA, ConstantInfo.toConstantVal,
                -ite_eq_left_iff, -ite_eq_right_iff,
                -Nat.max_eq_zero_iff] at hSr
              rw [← hSr] at hrmem
              exact hrmem
            · exact happM a hamem M hMmem'
        · refine ⟨SetTheory.lam (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            (fun r => r),
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              (fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)),
            ?_, ?_, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindR', hvalR',
              eqReflA, ConstantInfo.toConstantVal, Level.eval, u1N,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl
          · exact lam_mem (V := V)
              (B := fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r hr => hr
          · exact pi_mem_univ (u := ψ u1N) (v := ψ u1N)
              (B := fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              (happM a hamem M hMmem')
              (fun _ _ => happM a hamem M hMmem')
    · -- fibre-universe of the `a` λ
      refine ⟨SetTheory.lam (erB (ψ u1N))
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) (fun M =>
          SetTheory.lam (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            (fun r => r)),
        pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) (fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            (fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))),
        ?_, ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
          hfindR', hvalR', eqA, eqReflA, ConstantInfo.toConstantVal,
          Level.eval,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
      · refine lam_mem (V := V) (B := fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            (fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)))
          fun M hM => ?_
        have hM' : M ∈ˢ eqRecMSpace V (ψ u1N) A a := by
          rw [← hMSeq a hamem]
          exact hM
        exact lam_mem (V := V) (B := fun _ =>
          SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun r hr => hr
      · have hdom : (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
          rw [hMSeq a hamem]
          exact hMSmem a hamem
        have hfibs : ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) →
            (pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) ∈ˢ
              univ (ψ u1N) := by
          intro M hM
          have hM' : M ∈ˢ eqRecMSpace V (ψ u1N) A a := by
            rw [← hMSeq a hamem]
            exact hM
          have hrd := happM a hamem M hM'
          have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
            (B := fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            hrd (fun _ _ => hrd)
          by_cases hu1 : ψ u1N = 0
          · rw [if_pos hu1] at this
            exact hu1.symm ▸ this
          · rw [if_neg hu1] at this
            rw [show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from Nat.max_self _] at this
            exact this
        have hmem := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1))
          (v := ψ u1N)
          (B := fun M => pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          hdom hfibs
        by_cases hu1 : ψ u1N = 0
        · rw [if_pos hu1]
          rw [if_pos hu1] at hmem
          exact hmem
        · rw [if_neg hu1]
          rw [if_neg hu1, max_eqrec_b] at hmem
          exact hmem
  · -- fibre-universe of the `α` λ
    have hafib : ∀ a', a' ∈ˢ A →
        (pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a')
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a'))
            fun _ => SetTheory.app (SetTheory.app M a')
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a')) ∈ˢ
          univ (if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro a' ha'
      have hdom : (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
          fun _ => univ (ψ u1N)) ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
        rw [hMSeq a' ha']
        exact hMSmem a' ha'
      have hfibs : ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a') b)
          fun _ => univ (ψ u1N)) →
          (pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a')
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a'))
            fun _ => SetTheory.app (SetTheory.app M a')
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a')) ∈ˢ
            univ (ψ u1N) := by
        intro M hM
        have hM' : M ∈ˢ eqRecMSpace V (ψ u1N) A a' := by
          rw [← hMSeq a' ha']
          exact hM
        have hrd := happM a' ha' M hM'
        have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
          (B := fun _ => SetTheory.app (SetTheory.app M a')
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a'))
          hrd (fun _ _ => hrd)
        by_cases hu1 : ψ u1N = 0
        · rw [if_pos hu1] at this
          exact hu1.symm ▸ this
        · rw [if_neg hu1] at this
          rw [show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from Nat.max_self _] at this
          exact this
      have hmem := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1))
        (v := ψ u1N)
        (B := fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a')
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a'))
          fun _ => SetTheory.app (SetTheory.app M a')
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a'))
        hdom hfibs
      by_cases hu1 : ψ u1N = 0
      · rw [if_pos hu1]
        rw [if_pos hu1] at hmem
        exact hmem
      · rw [if_neg hu1]
        rw [if_neg hu1, max_eqrec_b] at hmem
        exact hmem
    refine ⟨SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A (fun a =>
      SetTheory.lam (erB (ψ u1N))
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) fun M =>
        SetTheory.lam (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun r => r),
      pi (eqRhsA' (ψ uN) (ψ u1N)) A (fun a =>
        pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)),
      ?_, ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE',
        hfindR', hvalR', eqA, eqReflA, ConstantInfo.toConstantVal,
        Level.eval,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · refine lam_mem (V := V) (B := fun a =>
        pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        fun a ha => ?_
      refine lam_mem (V := V) (B := fun M =>
        pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun _ => SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        fun M hM => ?_
      exact lam_mem (V := V) (B := fun _ =>
        SetTheory.app (SetTheory.app M a)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        fun r hr => hr
    · have hmem := pi_mem_univ (u := ψ uN)
        (v := if ψ u1N = 0 then 0 else Nat.max (ψ uN) (ψ u1N + 1))
        (B := fun a =>
          pi (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        hAmem hafib
      by_cases hu1 : ψ u1N = 0
      · rw [if_pos hu1]
        rw [show (if ψ u1N = 0 then 0
            else Nat.max (ψ uN) (ψ u1N + 1)) = 0 from if_pos hu1] at hmem
        rw [if_pos rfl] at hmem
        exact hmem
      · rw [if_neg hu1]
        have hne : (if ψ u1N = 0 then 0
            else Nat.max (ψ uN) (ψ u1N + 1)) ≠ 0 := by
          rw [if_neg hu1]
          exact max_ne_zero_r' (Nat.succ_ne_zero _)
        rw [if_neg hne, if_neg hu1] at hmem
        rw [show Nat.max (ψ uN) (Nat.max (ψ uN) (ψ u1N + 1)) =
          Nat.max (ψ uN) (ψ u1N + 1) from max_absorb_l' _ _] at hmem
        exact hmem


/-- The fold equation of `Eq.rec`'s rule: the recursor applied through
its telescope (with the major reduced to a reflexivity proof) equals
the rhs applied to the non-index prefix. -/
theorem eqRec_iota {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ')
    {Av av Mv rv bv hv : V}
    (hA : Av ∈ˢ univ (ψ uN)) (ha : av ∈ˢ Av)
    (hM : Mv ∈ˢ eqRecMSpace V (ψ u1N) Av av)
    (hr : rv ∈ˢ SetTheory.app (SetTheory.app Mv av) pt)
    (hb : bv ∈ˢ Av) (hh : hv ∈ˢ eqv av bv) :
    ∃ R, interpClosed V cval env ψ eqRecRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) bv)
        hv =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app R Av) av)
        Mv) rv := by
  refine ⟨_, interp_eqRec_rhs hfindE hvalE hfindR hvalR, ?_⟩
  obtain rfl : av = bv := mem_eqv hh
  obtain rfl : hv = pt := mem_univ_zero (eqv_mem_univ av av) hh
  by_cases h0 : ψ u1N = 0
  · -- Prop collapse: both sides are the proof point
    have hL : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) av)
        pt = pt := by
      have hval : eqRecVal V ψ = (pt : V) := by
        simp only [eqRecVal]
        refine lamC_of_forall fun A hA' => ?_
        refine lamC_of_forall fun a ha' => ?_
        refine lamC_of_forall fun M hM' => ?_
        have hM'' := hM'
        simp only [eqRecMSpace] at hM''
        have hMapt0 : SetTheory.app (SetTheory.app M a) pt ∈ˢ
            univ (ψ u1N) :=
          app_mem_piC (app_mem_piC hM'' ha') (pt_mem_eqv_self a)
        refine lamC_of_forall fun r hr' => ?_
        refine lamC_of_forall fun b hb' => ?_
        exact lamC_of_forall fun h hh' =>
          mem_univ_zero (h0 ▸ hMapt0) hr'
      rw [hval]
      simp only [app_pt]
    have hR : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
          SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
            SetTheory.lam (erB (ψ u1N))
              (pi (ψ u1N + 1) A fun b =>
                pi (ψ u1N + 1)
                  (SetTheory.app (SetTheory.app
                    (SetTheory.app (eqVal V ψ) A) a) b)
                  fun _ => univ (ψ u1N)) fun M =>
              SetTheory.lam (ψ u1N)
                (SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
                fun r => r) Av) av) Mv) rv = pt := by
      have hval : (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN))
          fun A =>
          SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
            SetTheory.lam (erB (ψ u1N))
              (pi (ψ u1N + 1) A fun b =>
                pi (ψ u1N + 1)
                  (SetTheory.app (SetTheory.app
                    (SetTheory.app (eqVal V ψ) A) a) b)
                  fun _ => univ (ψ u1N)) fun M =>
              SetTheory.lam (ψ u1N)
                (SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
                fun r => r) = (pt : V) := by
        refine lamC_of_forall fun A hA' => ?_
        refine lamC_of_forall fun a ha' => ?_
        refine lamC_of_forall fun M hM' => ?_
        have h1 : SetTheory.app M a ∈ˢ
            piC (SetTheory.app (SetTheory.app
              (SetTheory.app (eqVal V ψ) A) a) a)
              (fun _ => univ (ψ u1N)) :=
          app_mem_piC hM' ha'
        have h2 : SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a ∈ˢ
            SetTheory.app (SetTheory.app
              (SetTheory.app (eqVal V ψ) A) a) a := by
          rw [eqReflVal_app₂ hA' ha', eqVal_app₃ hA' ha' ha']
          exact pt_mem_eqv_self a
        have h3 := app_mem_piC h1 h2
        exact lamC_of_forall fun r hr' =>
          mem_univ_zero (h0 ▸ h3) hr'
      rw [hval]
      simp only [app_pt]
    rw [hL, hR]
  · -- data levels: both sides compute to the minor premise
    have hMv := hM
    simp only [eqRecMSpace] at hMv
    have hMafib : ∀ b', b' ∈ˢ Av →
        (pi (ψ u1N + 1) (eqv av b') fun _ => univ (ψ u1N)) ∈ˢ
          univ (ψ u1N + 1) :=
      fun b' hb' => pi_mem_univ (u := 0) (v := ψ u1N + 1)
        (B := fun _ => univ (ψ u1N))
        (eqv_mem_univ av b') (fun _ _ => univ_mem_univ (ψ u1N))
    have hMa : SetTheory.app Mv av ∈ˢ pi (ψ u1N + 1) (eqv av av)
        (fun _ => univ (ψ u1N)) := app_mem hMv ha hMafib
    have hMapt : SetTheory.app (SetTheory.app Mv av) pt ∈ˢ univ (ψ u1N) :=
      app_mem hMa (pt_mem_eqv_self av) (fun _ _ => univ_mem_univ (ψ u1N))
    -- parametric universe facts for the value-side telescopes
    have hMS : ∀ A : V, A ∈ˢ univ (ψ uN) → ∀ a : V, a ∈ˢ A →
        eqRecMSpace V (ψ u1N) A a ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      unfold eqRecMSpace
      exact pi_mem_univ (u := ψ uN) (v := ψ u1N + 1) hA'
        (fun b hb' => pi_mem_univ (u := 0) (v := ψ u1N + 1)
          (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a b) (fun _ _ => univ_mem_univ (ψ u1N)))
    have hMapt' : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        SetTheory.app (SetTheory.app M a) pt ∈ˢ univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      simp only [eqRecMSpace] at hM'
      have hMa' : SetTheory.app M a ∈ˢ pi (ψ u1N + 1) (eqv a a)
          (fun _ => univ (ψ u1N)) :=
        app_mem hM' ha' (fun b hb' => pi_mem_univ (u := 0) (v := ψ u1N + 1)
          (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a b) (fun _ _ => univ_mem_univ (ψ u1N)))
      exact app_mem hMa' (pt_mem_eqv_self a)
        (fun _ _ => univ_mem_univ (ψ u1N))
    have hT5 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        (pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N)) := by
      intro A hA' a ha' M hM'
      have h5 : ∀ b, b ∈ˢ A →
          (pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt) ∈ˢ univ (ψ u1N) := by
        intro b hb'
        have := pi_mem_univ (u := 0) (v := ψ u1N)
          (B := fun _ => SetTheory.app (SetTheory.app M a) pt)
          (eqv_mem_univ a b) (fun _ _ => hMapt' A hA' a ha' M hM')
        rw [if_neg h0] at this
        exact this
      have := pi_mem_univ (u := ψ uN) (v := ψ u1N)
        (B := fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt) hA' h5
      rw [if_neg h0] at this
      exact this
    have hwne : Nat.max (ψ uN) (ψ u1N) ≠ 0 :=
      max_ne_zero_r' h0
    have hT4 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        (pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M a) pt) fun _ =>
          pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N)) := by
      intro A hA' a ha' M hM'
      have := pi_mem_univ (u := ψ u1N) (v := Nat.max (ψ uN) (ψ u1N))
        (B := fun _ => pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt)
        (hMapt' A hA' a ha' M hM') (fun _ _ => hT5 A hA' a ha' M hM')
      rw [if_neg hwne] at this
      rw [show Nat.max (ψ u1N) (Nat.max (ψ uN) (ψ u1N)) =
        Nat.max (ψ uN) (ψ u1N) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_max_right _ _, Nat.le_refl _⟩)
          (Nat.le_max_right _ _)] at this
      exact this
    have hT3 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a) fun M =>
          pi (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun _ =>
            pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
              SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      have := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1))
        (v := Nat.max (ψ uN) (ψ u1N))
        (B := fun M => pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M a) pt) fun _ =>
          pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt)
        (hMS A hA' a ha') (fun M hM' => hT4 A hA' a ha' M hM')
      rw [if_neg hwne] at this
      rw [show Nat.max (Nat.max (ψ uN) (ψ u1N + 1)) (Nat.max (ψ uN) (ψ u1N)) =
        Nat.max (ψ uN) (ψ u1N + 1) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_refl _,
            Nat.max_le.mpr ⟨Nat.le_max_left _ _,
              Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)⟩⟩)
          (Nat.le_max_left _ _)] at this
      exact this
    -- the left fold
    have hL : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) av)
        pt = rv := by
      simp only [eqRecVal, if_neg h0]
      have h1 := app_lam (v := Nat.max (ψ uN) (ψ u1N + 1)) (a := Av)
        (A := univ (ψ uN)) hA
        (B := fun A => pi (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          pi (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a) fun M =>
            pi (Nat.max (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a) pt) fun _ =>
              pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
                SetTheory.app (SetTheory.app M a) pt)
        (F := fun A => SetTheory.lam (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a)
            fun M => SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a) pt) fun r =>
              SetTheory.lam (ψ u1N) A fun _b =>
                SetTheory.lam (ψ u1N) (eqv a _b) fun _h => r)
        (fun A hA' => lam_mem (V := V) fun a ha' =>
          lam_mem (V := V) fun M hM' =>
            lam_mem (V := V) fun r hr' =>
              lam_mem (V := V) fun b hb' =>
                lam_mem (V := V) fun h hh' => hr')
        (fun A hA' => by
          have := pi_mem_univ (u := ψ uN) (v := Nat.max (ψ uN) (ψ u1N + 1))
            (B := fun a => pi (Nat.max (ψ uN) (ψ u1N))
              (eqRecMSpace V (ψ u1N) A a) fun M =>
              pi (Nat.max (ψ uN) (ψ u1N))
                (SetTheory.app (SetTheory.app M a) pt) fun _ =>
                pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
                  SetTheory.app (SetTheory.app M a) pt)
            hA' (fun a ha' => hT3 A hA' a ha')
          rw [if_neg (max_ne_zero_r' (Nat.succ_ne_zero _)),
            max_absorb_l'] at this
          exact this)
      rw [h1]
      have h2 := app_lam (v := Nat.max (ψ uN) (ψ u1N + 1)) (a := av)
        (A := Av) ha
        (B := fun a => pi (Nat.max (ψ uN) (ψ u1N))
          (eqRecMSpace V (ψ u1N) Av a) fun M =>
          pi (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun _ =>
            pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv a b) fun _ =>
              SetTheory.app (SetTheory.app M a) pt)
        (F := fun a => SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
          (eqRecMSpace V (ψ u1N) Av a) fun M =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun r =>
            SetTheory.lam (ψ u1N) Av fun _b =>
              SetTheory.lam (ψ u1N) (eqv a _b) fun _h => r)
        (fun a ha' => lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' =>
            lam_mem (V := V) fun b hb' =>
              lam_mem (V := V) fun h hh' => hr')
        (fun a ha' => hT3 Av hA a ha')
      rw [h2]
      have h3 := app_lam (v := Nat.max (ψ uN) (ψ u1N)) (a := Mv)
        (A := eqRecMSpace V (ψ u1N) Av av) hM
        (B := fun M => pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M av) pt) fun _ =>
          pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv av b) fun _ =>
            SetTheory.app (SetTheory.app M av) pt)
        (F := fun M => SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M av) pt) fun r =>
          SetTheory.lam (ψ u1N) Av fun _b =>
            SetTheory.lam (ψ u1N) (eqv av _b) fun _h => r)
        (fun M hM' => lam_mem (V := V) fun r hr' =>
          lam_mem (V := V) fun b hb' =>
            lam_mem (V := V) fun h hh' => hr')
        (fun M hM' => hT4 Av hA av ha M hM')
      rw [h3]
      have h4 := app_lam (v := Nat.max (ψ uN) (ψ u1N)) (a := rv)
        (A := SetTheory.app (SetTheory.app Mv av) pt) hr
        (B := fun _ => pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv av b) fun _ =>
          SetTheory.app (SetTheory.app Mv av) pt)
        (F := fun r => SetTheory.lam (ψ u1N) Av fun _b =>
          SetTheory.lam (ψ u1N) (eqv av _b) fun _h => r)
        (fun r hr' => lam_mem (V := V) fun b hb' =>
          lam_mem (V := V) fun h hh' => hr')
        (fun _ _ => hT5 Av hA av ha Mv hM)
      rw [h4]
      have h5 := app_lam (v := ψ u1N) (a := av) (A := Av) ha
        (B := fun b => pi (ψ u1N) (eqv av b) fun _ =>
          SetTheory.app (SetTheory.app Mv av) pt)
        (F := fun _b => SetTheory.lam (ψ u1N) (eqv av _b) fun _h => rv)
        (fun b hb' => lam_mem (V := V) fun h hh' => hr)
        (fun b hb' => by
          have := pi_mem_univ (u := 0) (v := ψ u1N)
            (B := fun _ => SetTheory.app (SetTheory.app Mv av) pt)
            (eqv_mem_univ av b) (fun _ _ => hMapt)
          rw [if_neg h0] at this
          exact this)
      rw [h5]
      exact app_lam (v := ψ u1N) (a := pt) (A := eqv av av)
        (pt_mem_eqv_self av)
        (B := fun _ => SetTheory.app (SetTheory.app Mv av) pt)
        (F := fun _h => rv)
        (fun _ _ => hr)
        (fun _ _ => hMapt)
    -- the right fold
    have hrd : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) →
        SetTheory.app (SetTheory.app M a)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a) ∈ˢ
          univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      rw [eqReflVal_app₂ hA' ha']
      refine hMapt' A hA' a ha' M ?_
      rw [← show (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a from by
          unfold eqRecMSpace
          exact pi_congr fun b hb' => by rw [eqVal_app₃ hA' ha' hb']]
      exact hM'
    have hMv' : Mv ∈ˢ (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) av) b)
        fun _ => univ (ψ u1N)) := by
      rw [show (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) av) b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) Av av from by
          unfold eqRecMSpace
          exact pi_congr fun b hb' => by rw [eqVal_app₃ hA ha hb']]
      exact hM
    have hrfib : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) →
        (pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun _ => SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) ∈ˢ
          univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
        (B := fun _ => SetTheory.app (SetTheory.app M a)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        (hrd A hA' a ha' M hM') (fun _ _ => hrd A hA' a ha' M hM')
      rw [if_neg h0,
        show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from Nat.max_self _] at this
      exact this
    have hMSi : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      rw [show (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
        fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a from by
          unfold eqRecMSpace
          exact pi_congr fun b hb' => by rw [eqVal_app₃ hA' ha' hb']]
      exact hMS A hA' a ha'
    have hT3r : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      rw [erB_eq]
      have := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1)) (v := ψ u1N)
        (B := fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun _ => SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        (hMSi A hA' a ha') (fun M hM' => hrfib A hA' a ha' M hM')
      rw [if_neg h0, max_eqrec_b] at this
      exact this
    have hR : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
          SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
            SetTheory.lam (erB (ψ u1N))
              (pi (ψ u1N + 1) A fun b =>
                pi (ψ u1N + 1)
                  (SetTheory.app (SetTheory.app
                    (SetTheory.app (eqVal V ψ) A) a) b)
                  fun _ => univ (ψ u1N)) fun M =>
              SetTheory.lam (ψ u1N)
                (SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
                fun r => r) Av) av) Mv) rv = rv := by
      have h1 := app_lam (v := eqRhsAl' (ψ uN) (ψ u1N)) (a := Av)
        (A := univ (ψ uN)) hA
        (B := fun A => pi (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          pi (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        (F := fun A => SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r)
        (fun A hA' => lam_mem (V := V) fun a ha' =>
          lam_mem (V := V) fun M hM' =>
            lam_mem (V := V) fun r hr' => hr')
        (fun A hA' => by
          rw [eqRhsAl'_eq, eqRhsA'_eq, if_neg h0]
          have := pi_mem_univ (u := ψ uN)
            (v := Nat.max (ψ uN) (ψ u1N + 1))
            (B := fun a => pi (erB (ψ u1N))
              (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
              pi (ψ u1N)
                (SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
                fun _ => SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            hA' (fun a ha' => hT3r A hA' a ha')
          rw [if_neg (max_ne_zero_r' (Nat.succ_ne_zero _)),
            max_absorb_l'] at this
          exact this)
      rw [h1]
      have h2 := app_lam (v := eqRhsA' (ψ uN) (ψ u1N)) (a := av)
        (A := Av) ha
        (B := fun a => pi (erB (ψ u1N))
          (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
        (F := fun a => SetTheory.lam (erB (ψ u1N))
          (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
            fun r => r)
        (fun a ha' => lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' => hr')
        (fun a ha' => by
          rw [eqRhsA'_eq, if_neg h0]
          exact hT3r Av hA a ha')
      rw [h2]
      have h3 := app_lam (v := erB (ψ u1N)) (a := Mv)
        (A := pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) av) b)
          fun _ => univ (ψ u1N)) hMv'
        (B := fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
          fun _ => SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
        (F := fun M => SetTheory.lam (ψ u1N)
          (SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
          fun r => r)
        (fun M hM' => lam_mem (V := V) fun r hr' => hr')
        (fun M hM' => by
          rw [erB_eq]
          exact hrfib Av hA av ha M hM')
      rw [h3]
      have hrveq : rv ∈ˢ SetTheory.app (SetTheory.app Mv av)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av) := by
        rw [eqReflVal_app₂ hA ha]
        exact hr
      exact app_lam (v := ψ u1N) (a := rv)
        (A := SetTheory.app (SetTheory.app Mv av)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av)) hrveq
        (B := fun _ => SetTheory.app (SetTheory.app Mv av)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
        (F := fun r => r)
        (fun r hr' => hr')
        (fun _ _ => hrd Av hA av ha Mv hMv')
    rw [hL, hR]

end Setlec
