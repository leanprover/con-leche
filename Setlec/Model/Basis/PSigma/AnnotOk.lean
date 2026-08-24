import Setlec.Model.Basis.PSigma.Iota

/-!
# Annotation truthfulness of the `PSigma'.rec` rule right-hand side
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-- The `PSigma'.rec` rule rhs carries truthful annotations. -/
theorem annotOk_psigmaRec_rhs {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) psigmaRecRhsA := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA := hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  have hfindM' : env.find? ((Name.anonymous.str "PSigma'").str "mk") = some psigmaMkA :=
    hfindM
  have hvalM' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PSigma'").str "mk") ψ' = psigmaMkVal V ψ' := hvalM
  simp only [psigmaRecRhsA, psigmaRecA, ConstantInfo.recRules, List.getD,
    List.getElem?_cons_zero, Option.getD_some, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro A SA hSA hAmem
  have hSA' : SA = univ (ψ uN) := by
    simp only [interpExpr, Level.eval, Option.some.injEq] at hSA
    rw [← hSA]
    rfl
  rw [hSA'] at hAmem
  have hsigU : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B ∈ˢ
        univ (Nat.max (ψ uN) (ψ vN)) := by
    intro B hB
    rw [psigmaVal_fold hAmem hB]
    exact sigma_mem_univ hAmem (fun x hx =>
      app_mem hB hx fun _ _ => univ_mem_univ (ψ vN))
  have hβdomU : (pi (ψ vN + 1) A fun _ => univ (ψ vN)) ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN + 1)) :=
    pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hAmem
      (fun _ _ => univ_mem_univ (ψ vN))
  have hMspU : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0) ∈ˢ
      univ (if 1 = 0 then 0 else Nat.max (Nat.max (ψ uN) (ψ vN)) 1) :=
    fun B hB => pi_mem_univ (u := Nat.max (ψ uN) (ψ vN)) (v := 1)
      (hsigU B hB) (fun _ _ => univ_mem_univ 0)
  -- the fully parametric β-slot tower fact
  have hmk4P : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      ∀ a, a ∈ˢ A → ∀ b, b ∈ˢ SetTheory.app B a →
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (psigmaMkVal V ψ) A) B) a) b ∈ˢ
      SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B := by
    intro B hB a ha b hb
    rw [psigmaVal_fold hAmem hB]
    exact psigmaMkVal_app₄_mem hAmem hB ha hb
  have happMP : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      ∀ M, M ∈ˢ (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0) →
      ∀ x, x ∈ˢ SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B →
      SetTheory.app M x ∈ˢ univ 0 :=
    fun B hB M hM x hx => app_mem hM hx (fun _ _ => univ_mem_univ 0)
  have ht3P : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      ∀ M, M ∈ˢ (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0) →
      (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) ∈ˢ univ 0 := by
    intro B hB M hM
    have := pi_mem_univ (u := ψ uN) (v := 0)
      (B := fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
      hAmem
      (fun a ha => by
        have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
          app_mem hB ha fun _ _ => univ_mem_univ (ψ vN)
        have := pi_mem_univ (u := ψ vN) (v := 0)
          (B := fun b => SetTheory.app M
            (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
          hBa (fun b hb => happMP B hB M hM _ (hmk4P B hB a ha b hb))
        rw [if_pos rfl] at this
        exact this)
    rw [if_pos rfl] at this
    exact this
  have ht2P : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      ∀ M, M ∈ˢ (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0) →
      (pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
        fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) ∈ˢ univ 0 := by
    intro B hB M hM
    have := pi_mem_univ (u := 0) (v := 0)
      (B := fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
      (ht3P B hB M hM) (fun _ _ => ht3P B hB M hM)
    rw [if_pos rfl] at this
    exact this
  have htBP : ∀ B : V, B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) →
      (pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0)
        fun M => pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
          fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) ∈ˢ
        univ 0 := by
    intro B hB
    have := pi_mem_univ
      (u := if 1 = 0 then 0 else Nat.max (Nat.max (ψ uN) (ψ vN)) 1)
      (v := 0)
      (B := fun M => pi 0 (pi 0 A fun a =>
        pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
        fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
      (hMspU B hB) (fun M hM => ht2P B hB M hM)
    rw [if_pos rfl] at this
    exact this
  refine ⟨?_, ?_⟩
  · -- the β-λ
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨?_, ⟨_, rfl⟩, ?_⟩
    · -- the binder type `(x : α) → Sort v`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
      intro x Sx hSx hxmem
      refine ⟨trivial, ?_⟩
      refine ⟨univ (ψ vN), ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, Level.eval, vN]
      · exact univ_mem_univ (ψ vN)
    · intro B SB hSB hBmem
      simp [interpExpr, Expr.instantiate1, updV,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSB
      subst hSB
      have hBmem' : B ∈ˢ pi (ψ vN + 1) A (fun _ => univ (ψ vN)) := hBmem
      refine ⟨?_, ?_⟩
      · -- the motive-λ
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨?_, ⟨_, rfl⟩, ?_⟩
        · -- the motive space `(t : PSigma' α β) → Prop`
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
              psigmaVal V ψ, A,
              Nat.max (Nat.max (ψ uN) (ψ vN + 1)) (Nat.max (ψ uN) (ψ vN) + 1),
              univ (ψ uN),
              (fun X => pi (Nat.max (ψ uN) (ψ vN) + 1)
                (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun _ =>
                  univ (Nat.max (ψ uN) (ψ vN))),
              ?_, ?_, psigmaVal_mem, hAmem, ?_⟩,
            (by simp [Expr.instantiate1, AnnotOk]),
            SetTheory.app (psigmaVal V ψ) A, B,
            Nat.max (ψ uN) (ψ vN) + 1,
            pi (ψ vN + 1) A (fun _ => univ (ψ vN)),
            (fun _ => univ (Nat.max (ψ uN) (ψ vN))),
            ?_, ?_, psigmaVal_app_mem hAmem, hBmem',
            fun _ _ => univ_mem_univ (Nat.max (ψ uN) (ψ vN))⟩,
            ⟨_, rfl⟩, ?_⟩
          · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
              psigmaA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
          · intro X hX
            have hdom : (pi (ψ vN + 1) X fun _ => univ (ψ vN)) ∈ˢ
                univ (Nat.max (ψ uN) (ψ vN + 1)) :=
              pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hX
                (fun _ _ => univ_mem_univ (ψ vN))
            exact pi_mem_univ (u := Nat.max (ψ uN) (ψ vN + 1))
              (v := Nat.max (ψ uN) (ψ vN) + 1) hdom
              (fun _ _ => univ_mem_univ (Nat.max (ψ uN) (ψ vN)))
          · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
              psigmaA, ConstantInfo.toConstantVal]
            try rfl
          · simp [interpExpr, Expr.instantiate1, updV]
          · intro t St hSt htmem
            refine ⟨trivial, ?_⟩
            refine ⟨univ 0, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
            · exact univ_mem_univ 0
        · intro M SM hSM hMmem
          simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            psigmaA, ConstantInfo.toConstantVal, Level.eval,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSM
          subst hSM
          have hMmem' : M ∈ˢ pi 1
              (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
              (fun _ => univ 0) := hMmem
          have happM := happMP B hBmem' M hMmem'
          have hmk4 := hmk4P B hBmem'
          refine ⟨?_, ?_⟩
          · -- the mk-λ
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨?_, ⟨_, rfl⟩, ?_⟩
            · -- the minor-premise space
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ⟨_, rfl⟩, ?_⟩
              intro a Sa hSa hamem
              simp [interpExpr, Expr.instantiate1, updV] at hSa
              subst hSa
              refine ⟨?_, ?_⟩
              · -- opened `∀ (snd : β fst), motive (mk …)`
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                  (by simp [Expr.instantiate1, AnnotOk]), B, a, ψ vN + 1, A,
                  (fun _ => univ (ψ vN)), ?_, ?_, hBmem', hamem,
                  fun _ _ => univ_mem_univ (ψ vN)⟩, ⟨_, rfl⟩, ?_⟩
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
                      (if Nat.max (ψ uN) (ψ vN) = 0 then 0
                        else Nat.max (ψ uN) (ψ vN + 1)),
                      univ (ψ uN),
                      (fun X => pi (Nat.max (ψ uN) (ψ vN))
                        (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun B' =>
                          pi (Nat.max (ψ uN) (ψ vN)) X fun a' =>
                            pi (Nat.max (ψ uN) (ψ vN))
                              (SetTheory.app B' a') fun _ =>
                              sigmaSet (Nat.max (ψ uN) (ψ vN)) X fun x =>
                                SetTheory.app B' x),
                      ?_, ?_, psigmaMkVal_mem, hAmem,
                      fun X hX => psigmaMk_space1 hX⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (psigmaMkVal V ψ) A, B,
                      Nat.max (ψ uN) (ψ vN),
                      pi (ψ vN + 1) A (fun _ => univ (ψ vN)),
                      (fun B' => pi (Nat.max (ψ uN) (ψ vN)) A fun a' =>
                        pi (Nat.max (ψ uN) (ψ vN))
                          (SetTheory.app B' a') fun _ =>
                          sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
                            SetTheory.app B' x),
                      ?_, ?_, psigmaMkVal_app_mem hAmem, hBmem',
                      fun B' hB' => psigmaMk_space2 hAmem hB'⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B,
                      a, Nat.max (ψ uN) (ψ vN), A,
                      (fun a' => pi (Nat.max (ψ uN) (ψ vN))
                        (SetTheory.app B a') fun _ =>
                        sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
                          SetTheory.app B x),
                      ?_, ?_, psigmaMkVal_app₂_mem hAmem hBmem', hamem,
                      fun a' ha' => psigmaMk_space3 hAmem hBmem' ha'⟩,
                    (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app (SetTheory.app (SetTheory.app
                        (psigmaMkVal V ψ) A) B) a,
                      b, Nat.max (ψ uN) (ψ vN), SetTheory.app B a,
                      (fun _ => sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
                        SetTheory.app B x),
                      ?_, ?_, psigmaMkVal_app₃_mem hAmem hBmem' hamem, hbmem,
                      fun _ _ => sigma_mem_univ hAmem (fun x hx =>
                        app_mem hBmem' hx fun _ _ => univ_mem_univ (ψ vN))⟩,
                    M,
                    SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
                      (psigmaMkVal V ψ) A) B) a) b,
                    1,
                    SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B,
                    (fun _ => univ 0),
                    ?_, ?_, hMmem', hmk4 a hamem b hbmem,
                    fun _ _ => univ_mem_univ 0⟩
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
                      a) b), ?_, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                      hvalM', psigmaMkA, ConstantInfo.toConstantVal]
                    try rfl
                  · exact happM _ (hmk4 a hamem b hbmem)
              · -- fibre-universe of `fst` (annotation `imax v 0`)
                refine ⟨pi 0 (SetTheory.app B a) (fun b =>
                  SetTheory.app M (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                      a) b)), ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV, hfindM',
                    hvalM', psigmaMkA, ConstantInfo.toConstantVal, Level.eval,
                    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
                  try rfl
                · have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
                    app_mem hBmem' hamem fun _ _ => univ_mem_univ (ψ vN)
                  exact pi_mem_univ (u := ψ vN) (v := 0) hBa
                    (fun b hb => happM _ (hmk4 a hamem b hb))
            · intro m Sm hSm hmmem
              simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
                hfindM', hvalM', psigmaA, psigmaMkA,
                ConstantInfo.toConstantVal, Level.eval,
                -ite_eq_left_iff, -ite_eq_right_iff,
                -Nat.max_eq_zero_iff] at hSm
              subst hSm
              have hmmem' : m ∈ˢ pi 0 A fun a =>
                  pi 0 (SetTheory.app B a) fun b =>
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                        a) b) := hmmem
              have hma : ∀ a, a ∈ˢ A → SetTheory.app m a ∈ˢ
                  pi 0 (SetTheory.app B a) fun b =>
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                        a) b) := by
                intro a ha
                refine app_mem hmmem' ha (fun a' ha' => ?_)
                have hBa : SetTheory.app B a' ∈ˢ univ (ψ vN) :=
                  app_mem hBmem' ha' fun _ _ => univ_mem_univ (ψ vN)
                have := pi_mem_univ (u := ψ vN) (v := 0)
                  (B := fun b => SetTheory.app M
                    (SetTheory.app (SetTheory.app (SetTheory.app
                      (SetTheory.app (psigmaMkVal V ψ) A) B) a') b))
                  hBa (fun b hb => happM _ (hmk4 a' ha' b hb))
                rw [if_pos rfl] at this
                exact this
              have hmab : ∀ a, a ∈ˢ A → ∀ b, b ∈ˢ SetTheory.app B a →
                  SetTheory.app (SetTheory.app m a) b ∈ˢ
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                        a) b) := by
                intro a ha b hb
                exact app_mem (hma a ha) hb
                  (fun b' hb' => happM _ (hmk4 a ha b' hb'))
              refine ⟨?_, ?_⟩
              · -- the fst-λ
                try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
                intro a Sa hSa hamem
                have hSa' : Sa = A := by
                  simp [interpExpr, Expr.instantiate1, updV,
                    -ite_eq_left_iff, -ite_eq_right_iff,
                    -Nat.max_eq_zero_iff] at hSa
                  exact hSa.symm
                rw [hSa'] at hamem
                refine ⟨?_, ?_⟩
                · -- the snd-λ
                  try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                  refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                    (by simp [Expr.instantiate1, AnnotOk]),
                    B, a, ψ vN + 1, A, (fun _ => univ (ψ vN)),
                    ?_, ?_, hBmem', hamem,
                    fun _ _ => univ_mem_univ (ψ vN)⟩, ⟨_, rfl⟩, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV]
                  · simp [interpExpr, Expr.instantiate1, updV]
                  intro b Sb hSb hbmem
                  have hSb' : Sb = SetTheory.app B a := by
                    simp [interpExpr, Expr.instantiate1, updV,
                      -ite_eq_left_iff, -ite_eq_right_iff,
                      -Nat.max_eq_zero_iff] at hSb
                    exact hSb.symm
                  rw [hSb'] at hbmem
                  refine ⟨?_, ?_⟩
                  · -- the body `mk fst snd`
                    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
                    refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                      (by simp [Expr.instantiate1, AnnotOk]),
                      m, a, 0, A,
                      (fun a' => pi 0 (SetTheory.app B a') fun b' =>
                        SetTheory.app M (SetTheory.app (SetTheory.app
                          (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                            A) B) a') b')),
                      ?_, ?_, hmmem', hamem,
                      (fun a' ha' => by
                        try dsimp only
                        have hBa : SetTheory.app B a' ∈ˢ univ (ψ vN) :=
                          app_mem hBmem' ha' fun _ _ =>
                            univ_mem_univ (ψ vN)
                        have := pi_mem_univ (u := ψ vN) (v := 0)
                          (B := fun b' => SetTheory.app M
                            (SetTheory.app (SetTheory.app (SetTheory.app
                              (SetTheory.app (psigmaMkVal V ψ) A) B)
                                a') b'))
                          hBa (fun b' hb' =>
                            happM _ (hmk4 a' ha' b' hb'))
                        rw [if_pos rfl] at this
                        exact this)⟩,
                      (by simp [Expr.instantiate1, AnnotOk]),
                      SetTheory.app m a, b, 0, SetTheory.app B a,
                      (fun b' => SetTheory.app M
                        (SetTheory.app (SetTheory.app (SetTheory.app
                          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b')),
                      ?_, ?_, hma a hamem, hbmem,
                      (fun b' hb' => happM _ (hmk4 a hamem b' hb'))⟩
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · simp [interpExpr, Expr.instantiate1, updV]
                    · simp [interpExpr, Expr.instantiate1, updV]
                  · -- snd-cod slot (annotation `0`)
                    refine ⟨SetTheory.app (SetTheory.app m a) b,
                      SetTheory.app M (SetTheory.app (SetTheory.app
                        (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                          A) B) a) b),
                      ?_, hmab a hamem b hbmem,
                      happM _ (hmk4 a hamem b hbmem)⟩
                    simp [interpExpr, Expr.instantiate1, updV]
                · -- fst-cod slot (annotation `imax v 0`)
                  refine ⟨SetTheory.lam 0 (SetTheory.app B a) fun b =>
                    SetTheory.app (SetTheory.app m a) b,
                    pi 0 (SetTheory.app B a) fun b =>
                      SetTheory.app M (SetTheory.app (SetTheory.app
                        (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                          A) B) a) b),
                    ?_, ?_, ?_⟩
                  · simp [interpExpr, Expr.instantiate1, updV,
                      -ite_eq_left_iff, -ite_eq_right_iff,
                      -Nat.max_eq_zero_iff]
                    try rfl
                  · exact lam_mem (V := V)
                      (B := fun b => SetTheory.app M
                        (SetTheory.app (SetTheory.app (SetTheory.app
                          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
                      fun b hb => hmab a hamem b hb
                  · have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
                      app_mem hBmem' hamem fun _ _ => univ_mem_univ (ψ vN)
                    have := pi_mem_univ (u := ψ vN) (v := 0)
                      (B := fun b => SetTheory.app M
                        (SetTheory.app (SetTheory.app (SetTheory.app
                          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
                      hBa (fun b hb => happM _ (hmk4 a hamem b hb))
                    rw [if_pos rfl] at this
                    exact this
              · -- mk-cod slot (annotation `imax u (imax v 0)`)
                refine ⟨SetTheory.lam 0 A fun a =>
                  SetTheory.lam 0 (SetTheory.app B a) fun b =>
                    SetTheory.app (SetTheory.app m a) b,
                  pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                        A) B) a) b),
                  ?_, ?_, ?_⟩
                · simp [interpExpr, Expr.instantiate1, updV,
                    -ite_eq_left_iff, -ite_eq_right_iff,
                    -Nat.max_eq_zero_iff]
                  try rfl
                · exact lam_mem (V := V)
                    (B := fun a => pi 0 (SetTheory.app B a) fun b =>
                      SetTheory.app M (SetTheory.app (SetTheory.app
                        (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                          A) B) a) b))
                    fun a ha => lam_mem (V := V)
                      (B := fun b => SetTheory.app M
                        (SetTheory.app (SetTheory.app (SetTheory.app
                          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
                      fun b hb => hmab a ha b hb
                · exact ht3P B hBmem' M hMmem'
          · -- motive-cod slot
            refine ⟨SetTheory.lam 0 (pi 0 A fun a =>
              pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app
                  (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                    a) b))
              fun mk => SetTheory.lam 0 A fun a =>
                SetTheory.lam 0 (SetTheory.app B a) fun b =>
                  SetTheory.app (SetTheory.app mk a) b,
              pi 0 (pi 0 A fun a =>
                pi 0 (SetTheory.app B a) fun b =>
                  SetTheory.app M (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                      a) b))
              fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app
                  (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                    a) b),
              ?_, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindM', hvalM',
                psigmaMkA, ConstantInfo.toConstantVal, Level.eval,
                -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              try rfl
            · refine lam_mem (V := V)
                (B := fun _ => pi 0 A fun a =>
                  pi 0 (SetTheory.app B a) fun b =>
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                        A) B) a) b))
                fun mk hmk => ?_
              have hmka : ∀ a, a ∈ˢ A → SetTheory.app mk a ∈ˢ
                  pi 0 (SetTheory.app B a) fun b =>
                    SetTheory.app M (SetTheory.app (SetTheory.app
                      (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                        A) B) a) b) := by
                intro a ha
                refine app_mem hmk ha (fun a' ha' => ?_)
                have hBa : SetTheory.app B a' ∈ˢ univ (ψ vN) :=
                  app_mem hBmem' ha' fun _ _ => univ_mem_univ (ψ vN)
                have := pi_mem_univ (u := ψ vN) (v := 0)
                  (B := fun b' => SetTheory.app M
                    (SetTheory.app (SetTheory.app (SetTheory.app
                      (SetTheory.app (psigmaMkVal V ψ) A) B) a') b'))
                  hBa (fun b' hb' => happM _ (hmk4 a' ha' b' hb'))
                rw [if_pos rfl] at this
                exact this
              refine lam_mem (V := V)
                (B := fun a => pi 0 (SetTheory.app B a) fun b =>
                  SetTheory.app M (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app (psigmaMkVal V ψ)
                      A) B) a) b))
                fun a ha => ?_
              refine lam_mem (V := V)
                (B := fun b => SetTheory.app M
                  (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
                fun b hb => ?_
              exact app_mem (hmka a ha) hb
                (fun b' hb' => happM _ (hmk4 a ha b' hb'))
            · exact ht2P B hBmem' M hMmem'
      · -- β-cod slot
        refine ⟨SetTheory.lam 0
          (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            fun _ => univ 0)
          fun M => SetTheory.lam 0 (pi 0 A fun a =>
            pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun mk => SetTheory.lam 0 A fun a =>
              SetTheory.lam 0 (SetTheory.app B a) fun b =>
                SetTheory.app (SetTheory.app mk a) b,
          pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            fun _ => univ 0)
          fun M => pi 0 (pi 0 A fun a =>
            pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b),
          ?_, ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
            hfindM', hvalM', psigmaA, psigmaMkA,
            ConstantInfo.toConstantVal, Level.eval,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · refine lam_mem (V := V)
            (B := fun M => pi 0 (pi 0 A fun a =>
              pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app
                  (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                    a) b))
              fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app
                  (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                    a) b))
            fun M hM => ?_
          have happM := happMP B hBmem' M hM
          refine lam_mem (V := V)
            (B := fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun mk hmk => ?_
          have hmka : ∀ a, a ∈ˢ A → SetTheory.app mk a ∈ˢ
              pi 0 (SetTheory.app B a) fun b =>
                SetTheory.app M (SetTheory.app (SetTheory.app
                  (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                    a) b) := by
            intro a ha
            refine app_mem hmk ha (fun a' ha' => ?_)
            have hBa : SetTheory.app B a' ∈ˢ univ (ψ vN) :=
              app_mem hBmem' ha' fun _ _ => univ_mem_univ (ψ vN)
            have := pi_mem_univ (u := ψ vN) (v := 0)
              (B := fun b' => SetTheory.app M
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (psigmaMkVal V ψ) A) B) a') b'))
              hBa (fun b' hb' =>
                happM _ (hmk4P B hBmem' a' ha' b' hb'))
            rw [if_pos rfl] at this
            exact this
          refine lam_mem (V := V)
            (B := fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun a ha => ?_
          refine lam_mem (V := V)
            (B := fun b => SetTheory.app M
              (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
            fun b hb => ?_
          exact app_mem (hmka a ha) hb
            (fun b' hb' => happM _ (hmk4P B hBmem' a ha b' hb'))
        · exact htBP B hBmem'
  · -- α-cod slot
    refine ⟨SetTheory.lam 0 (pi (ψ vN + 1) A fun _ => univ (ψ vN))
      fun B => SetTheory.lam 0
        (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
          fun _ => univ 0)
        fun M => SetTheory.lam 0 (pi 0 A fun a =>
          pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b))
          fun mk => SetTheory.lam 0 A fun a =>
            SetTheory.lam 0 (SetTheory.app B a) fun b =>
              SetTheory.app (SetTheory.app mk a) b,
      pi 0 (pi (ψ vN + 1) A fun _ => univ (ψ vN))
      fun B => pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ)
          A) B) fun _ => univ 0)
        fun M => pi 0 (pi 0 A fun a =>
          pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b))
          fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b),
      ?_, ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
        hfindM', hvalM', psigmaA, psigmaMkA,
        ConstantInfo.toConstantVal, Level.eval, uN, vN,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · refine lam_mem (V := V)
        (B := fun B => pi 0 (pi 1 (SetTheory.app (SetTheory.app
            (psigmaVal V ψ) A) B) fun _ => univ 0)
          fun M => pi 0 (pi 0 A fun a =>
            pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
        fun B hB => ?_
      refine lam_mem (V := V)
        (B := fun M => pi 0 (pi 0 A fun a =>
          pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b))
          fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b))
        fun M hM => ?_
      have happM := happMP B hB M hM
      refine lam_mem (V := V)
        (B := fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app
            (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
              a) b))
        fun mk hmk => ?_
      have hmka : ∀ a, a ∈ˢ A → SetTheory.app mk a ∈ˢ
          pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app
              (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                a) b) := by
        intro a ha
        refine app_mem hmk ha (fun a' ha' => ?_)
        have hBa : SetTheory.app B a' ∈ˢ univ (ψ vN) :=
          app_mem hB ha' fun _ _ => univ_mem_univ (ψ vN)
        have := pi_mem_univ (u := ψ vN) (v := 0)
          (B := fun b' => SetTheory.app M
            (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (psigmaMkVal V ψ) A) B) a') b'))
          hBa (fun b' hb' => happM _ (hmk4P B hB a' ha' b' hb'))
        rw [if_pos rfl] at this
        exact this
      refine lam_mem (V := V)
        (B := fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app
            (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
              a) b))
        fun a ha => ?_
      refine lam_mem (V := V)
        (B := fun b => SetTheory.app M
          (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
        fun b hb => ?_
      exact app_mem (hmka a ha) hb
        (fun b' hb' => happM _ (hmk4P B hB a ha b' hb'))
    · have := pi_mem_univ (u := Nat.max (ψ uN) (ψ vN + 1)) (v := 0)
        (B := fun B => pi 0 (pi 1 (SetTheory.app (SetTheory.app
            (psigmaVal V ψ) A) B) fun _ => univ 0)
          fun M => pi 0 (pi 0 A fun a =>
            pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
            fun _ => pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M (SetTheory.app (SetTheory.app
                (SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B)
                  a) b))
        hβdomU (fun B hB => htBP B hB)
      rw [if_pos rfl] at this
      exact this

end Setlec
