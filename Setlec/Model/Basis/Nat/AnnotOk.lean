import Setlec.Model.Basis.Nat.Iota

/-!
# Annotation truthfulness of the `Nat.rec` rule right-hand sides
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-- The `Nat.rec` zero rule rhs carries truthful annotations. -/
theorem annotOk_natRecZero_rhs {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) natRecZeroRhsA := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") = some natZeroA :=
    hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") = some natSuccA :=
    hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' := hvalSc
  simp only [natRecZeroRhsA, natRecA, ConstantInfo.recRules, List.getD,
    List.getElem?_cons_zero, Option.getD_some, AnnotOk]
  refine ⟨?_, nrM (ψ uN), ?_⟩
  · -- the motive space `(t : Nat) → Sort u`
    try simp only [AnnotOk]
    refine ⟨trivial, ψ uN + 1, ?_⟩
    intro t A hA ht
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
    refine ⟨univ (ψ uN), ?_, ?_⟩
    · simp [Expr.instantiate1, interpExpr, Level.eval, uN]
    · exact univ_mem_univ (ψ uN)
  · intro M A hA hM
    have hA' : A = pi (ψ uN + 1) omega fun _ => univ (ψ uN) := by
      have : interpExpr V cval env ψ 0 (rho0 V)
          (Expr.forallE (Name.anonymous.str "t")
            (Expr.const (Name.anonymous.str "Nat") [])
            (Expr.sort (Level.param (Name.anonymous.str "u")))
            ⟨BinderInfo.default, some (Level.succ (Level.param (Name.anonymous.str "u")))⟩) =
          some (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) := by
        simp only [interpExpr, hfindN', hvalN', natA, ConstantInfo.toConstantVal,
          List.length_cons, List.length_nil, reduceIte, Level.eval, Level.substFn]
        simp [interpExpr, Expr.instantiate1, updV, uN]
        rfl
      rw [this] at hA
      exact (Option.some.inj hA).symm
    subst hA'
    have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app M n ∈ˢ univ (ψ uN) :=
      fun n hn' => app_mem hM hn' (fun _ _ => univ_mem_univ (ψ uN))
    have hMz : SetTheory.app M natzero ∈ˢ univ (ψ uN) :=
      hMfib natzero natzero_mem
    have hsfib : ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro n hn
      have := pi_mem_univ (u := ψ uN) (v := ψ uN)
        (B := fun _ => SetTheory.app M (natsucc n))
        (hMfib n hn)
        (fun _ _ => hMfib (natsucc n) (natsucc_mem hn))
      by_cases hu : ψ uN = 0
      · simpa [hu] using this
      · rw [if_neg hu, show Nat.max (ψ uN) (ψ uN) = ψ uN from
          Nat.max_self _] at this
        exact this
    -- the successor space: raw fibres fold to `natsucc` fibres
    have hSspEq : (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
        (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) :=
      pi_congr fun n hn => by rw [natSuccVal_app hn]
    have hSsp : (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
        univ (nrZ (ψ uN)) := by
      rw [hSspEq, enUU_eq, nrZ_eq]
      by_cases hu : ψ uN = 0
      · rw [if_pos hu]
        have := pi_mem_univ (u := 1) (v := ψ uN)
          (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n))
          (omega_mem_univ (V := V)) hsfib
        rw [if_pos hu] at this
        exact hu ▸ this
      · rw [if_neg hu]
        have := pi_mem_univ (u := 1) (v := ψ uN)
          (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n))
          (omega_mem_univ (V := V)) hsfib
        rw [if_neg hu] at this
        exact this
    -- the s-λ's pi type sits in the z-cod universe
    have hBin : (pi (ψ uN)
        (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
        (fun _ => SetTheory.app M natzero)) ∈ˢ
        univ (nrZ (ψ uN)) := by
      rw [nrZ_eq]
      have hSsp' := hSsp
      rw [nrZ_eq] at hSsp'
      by_cases hu : ψ uN = 0
      · rw [if_pos hu]
        rw [if_pos hu] at hSsp'
        have := pi_mem_univ (u := 0) (v := ψ uN)
          (B := fun _ => SetTheory.app M natzero)
          hSsp' (fun _ _ => hMz)
        rw [if_pos hu] at this
        exact hu ▸ this
      · rw [if_neg hu]
        rw [if_neg hu] at hSsp'
        have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
          (B := fun _ => SetTheory.app M natzero)
          hSsp' (fun _ _ => hMz)
        rw [if_neg hu,
          show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
            Nat.le_antisymm
              (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
              (Nat.le_max_left _ _)] at this
        exact this
    refine ⟨?_, ?_⟩
    · -- the z-λ over `motive Nat.zero`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
        (by simp [Expr.instantiate1, AnnotOk]),
        M, natzero, ψ uN + 1, omega, (fun _ => univ (ψ uN)),
        ?_, ?_, hM, natzero_mem,
        fun _ _ => univ_mem_univ (ψ uN)⟩, nrZ (ψ uN), ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV]
      · simp [interpExpr, Expr.instantiate1, updV, hfindZ', hvalZ',
          natZeroA, ConstantInfo.toConstantVal]
        try rfl
      intro z Az hAz hz
      have hAz' : Az = SetTheory.app M natzero := by
        simp [interpExpr, Expr.instantiate1, updV, hfindZ', hvalZ',
          natZeroA, ConstantInfo.toConstantVal,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hAz
        exact hAz.symm
      rw [hAz'] at hz
      refine ⟨?_, ?_⟩
      · -- the s-λ over the successor space
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨?_, ψ uN, ?_⟩
        · -- the successor space is annotation-truthful
          try simp only [AnnotOk]
          refine ⟨trivial,
            (if ψ uN = 0 then 0 else Nat.max (ψ uN) (ψ uN)), ?_⟩
          intro n An hAn hn
          have hAn' : An = omega := by
            simp [interpExpr, hfindN', hvalN', natA,
              ConstantInfo.toConstantVal,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hAn
            exact hAn.symm
          rw [hAn'] at hn
          refine ⟨?_, ?_⟩
          · -- the ih-∀ inside the successor space
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
              (by simp [Expr.instantiate1, AnnotOk]),
              M, n, ψ uN + 1, omega, (fun _ => univ (ψ uN)),
              ?_, ?_, hM, hn, fun _ _ => univ_mem_univ (ψ uN)⟩,
              ψ uN, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
            intro ih Aih hAih hih
            refine ⟨?_, ?_⟩
            · -- the body `motive (Nat.succ n)` of the ih-∀
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                ⟨(by simp [Expr.instantiate1, AnnotOk]),
                (by simp [Expr.instantiate1, AnnotOk]),
                natSuccVal V ψ, n, 1, omega, (fun _ => omega),
                ?_, ?_, natSuccVal_mem, hn, fun _ _ => omega_mem_univ⟩,
                M, SetTheory.app (natSuccVal V ψ) n,
                ψ uN + 1, omega, (fun _ => univ (ψ uN)),
                ?_, ?_, hM, ?_, fun _ _ => univ_mem_univ (ψ uN)⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · rw [natSuccVal_app hn]
                exact natsucc_mem hn
            · refine ⟨SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
                ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · rw [natSuccVal_app hn]
                exact hMfib (natsucc n) (natsucc_mem hn)
          · refine ⟨pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                hvalSc', natSuccA, ConstantInfo.toConstantVal,
                Level.eval, uN,
                -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              try rfl
            · rw [show (pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
                  (pi (ψ uN) (SetTheory.app M n) fun _ =>
                    SetTheory.app M (natsucc n)) from
                pi_congr fun _ _ => by rw [natSuccVal_app hn]]
              have := pi_mem_univ (u := ψ uN) (v := ψ uN)
                (B := fun _ => SetTheory.app M (natsucc n))
                (hMfib n hn)
                (fun _ _ => hMfib (natsucc n) (natsucc_mem hn))
              exact this
        · intro s As hAs hs
          refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
          refine ⟨z, SetTheory.app M natzero, ?_, hz, hMz⟩
          simp [interpExpr, Expr.instantiate1, updV]
      · -- z-cod slot: the s-λ's value and pi type
        refine ⟨SetTheory.lam (ψ uN)
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          (fun _s => z),
          pi (ψ uN)
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          (fun _ => SetTheory.app M natzero), ?_, ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
            hfindZ', hvalZ', hfindSc', hvalSc', natA, natZeroA, natSuccA,
            ConstantInfo.toConstantVal, Level.eval, uN,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · exact lam_mem (V := V)
            (B := fun _ => SetTheory.app M natzero) fun _ _ => hz
        · exact hBin
    · -- motive-cod slot: the z-λ pack's value and pi type
      refine ⟨SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            (fun _s => z),
        pi (nrZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            (fun _ => SetTheory.app M natzero), ?_, ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
          hfindZ', hvalZ', hfindSc', hvalSc', natA, natZeroA, natSuccA,
          ConstantInfo.toConstantVal, Level.eval, uN,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
      · exact lam_mem (V := V)
          (B := fun _ => pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            (fun _ => SetTheory.app M natzero))
          fun z hz => lam_mem (V := V)
            (B := fun _ => SetTheory.app M natzero) fun _ _ => hz
      · rw [nrM_eq]
        have hBin' := hBin
        rw [nrZ_eq] at hBin'
        by_cases hu : ψ uN = 0
        · rw [if_pos hu]
          rw [if_pos hu] at hBin'
          rw [show nrZ (ψ uN) = 0 from by rw [nrZ_eq, if_pos hu]]
          have := pi_mem_univ (u := ψ uN) (v := 0)
            (B := fun _ => pi (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              (fun _ => SetTheory.app M natzero))
            hMz (fun _ _ => hBin')
          rw [if_pos rfl] at this
          exact this
        · rw [if_neg hu]
          rw [if_neg hu] at hBin'
          rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
            rw [nrZ_eq, if_neg hu]]
          have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
            (B := fun _ => pi (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              (fun _ => SetTheory.app M natzero))
            hMz (fun _ _ => hBin')
          rw [if_neg (max_ne_zero_l (by decide) : Nat.max 1 (ψ uN) ≠ 0),
            max_absorb_r' 1 (ψ uN)] at this
          exact this



/-- The `Nat.rec` successor rule rhs carries truthful annotations. -/
theorem annotOk_natRecSucc_rhs {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    (hfindR : env.find? (natName.str "rec") = some natRecA)
    (hvalR : ∀ ψ' : Name → Nat, cval (natName.str "rec") ψ' = natRecVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) natRecSuccRhsA := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") = some natZeroA :=
    hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") = some natSuccA :=
    hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' := hvalSc
  have hfindR' : env.find? ((Name.anonymous.str "Nat").str "rec") = some natRecA :=
    hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "rec") ψ' = natRecVal V ψ' := hvalR
  -- the recursor's value inhabits its interpreted type
  obtain ⟨Trec, hTi, hRecT⟩ := natRec_key (env := env) (ψ := ψ)
    hfindN hvalN hfindZ hvalZ hfindSc hvalSc
  rw [interp_natRec_type hfindN hvalN hfindZ hvalZ hfindSc hvalSc] at hTi
  obtain rfl := Option.some.inj hTi
  -- parametric universe facts about an arbitrary motive
  have hMfibP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      ∀ n, n ∈ˢ omega → SetTheory.app M' n ∈ˢ univ (ψ uN) :=
    fun M' hM' n hn => app_mem hM' hn (fun _ _ => univ_mem_univ (ψ uN))
  have hrawP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      ∀ n, n ∈ˢ omega →
      SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n) ∈ˢ univ (ψ uN) := by
    intro M' hM' n hn
    rw [natSuccVal_app hn]
    exact hMfibP M' hM' (natsucc n) (natsucc_mem hn)
  have hsfibP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      ∀ n, n ∈ˢ omega →
      (pi (ψ uN) (SetTheory.app M' n) fun _ =>
        SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
        univ (ψ uN) := by
    intro M' hM' n hn
    have := pi_mem_univ (u := ψ uN) (v := ψ uN)
      (B := fun _ => SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
      (hMfibP M' hM' n hn) (fun _ _ => hrawP M' hM' n hn)
    by_cases hu : ψ uN = 0
    · simpa [hu] using this
    · rw [if_neg hu, show Nat.max (ψ uN) (ψ uN) = ψ uN from
        Nat.max_self _] at this
      exact this
  have hspP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app M' n) fun _ =>
          SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
        univ (en11UU (ψ uN)) := by
    intro M' hM'
    exact pi_mem_univ (u := 1) (v := enUU (ψ uN))
      (B := fun n => pi (ψ uN) (SetTheory.app M' n) fun _ =>
        SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
      omega_mem_univ
      (fun n hn => by
        try dsimp only
        rw [enUU_eq]
        exact hsfibP M' hM' n hn)
  have htTP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      (pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
        univ (en1U (ψ uN)) := by
    intro M' hM'
    exact pi_mem_univ (u := 1) (v := ψ uN)
      (B := fun t => SetTheory.app M' t)
      omega_mem_univ (fun t ht => hMfibP M' hM' t ht)
  have hs2P : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      (pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app M' n) fun _ =>
          SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
        fun _ => pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
        univ (enZ (ψ uN)) := by
    intro M' hM'
    exact pi_mem_univ (u := en11UU (ψ uN)) (v := en1U (ψ uN))
      (hspP M' hM') (fun _ _ => htTP M' hM')
  have hzTP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
      (pi (enZ (ψ uN)) (SetTheory.app M' natzero) fun _ =>
        pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
        univ (enM (ψ uN)) := by
    intro M' hM'
    exact pi_mem_univ (u := ψ uN) (v := enZ (ψ uN))
      (hMfibP M' hM' natzero natzero_mem) (fun _ _ => hs2P M' hM')
  simp only [natRecSuccRhsA, natRecA, ConstantInfo.recRules, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    AnnotOk]
  refine ⟨?_, enM (ψ uN), ?_⟩
  · -- the motive space `(t : Nat) → Sort u`
    try simp only [AnnotOk]
    refine ⟨trivial, ψ uN + 1, ?_⟩
    intro t A hA ht
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
    refine ⟨univ (ψ uN), ?_, ?_⟩
    · simp [Expr.instantiate1, interpExpr, Level.eval, uN]
    · exact univ_mem_univ (ψ uN)
  · intro M A hA hM
    have hA' : A = pi (ψ uN + 1) omega fun _ => univ (ψ uN) := by
      have : interpExpr V cval env ψ 0 (rho0 V)
          (Expr.forallE (Name.anonymous.str "t")
            (Expr.const (Name.anonymous.str "Nat") [])
            (Expr.sort (Level.param (Name.anonymous.str "u")))
            ⟨BinderInfo.default, some (Level.succ (Level.param (Name.anonymous.str "u")))⟩) =
          some (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) := by
        simp only [interpExpr, hfindN', hvalN', natA, ConstantInfo.toConstantVal,
          List.length_cons, List.length_nil, reduceIte, Level.eval, Level.substFn]
        simp [interpExpr, Expr.instantiate1, updV, uN]
        rfl
      rw [this] at hA
      exact (Option.some.inj hA).symm
    subst hA'
    have hMfib := hMfibP M hM
    have hMz : SetTheory.app M natzero ∈ˢ univ (ψ uN) :=
      hMfib natzero natzero_mem
    refine ⟨?_, ?_⟩
    · -- the z-λ over `motive Nat.zero`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
        (by simp [Expr.instantiate1, AnnotOk]),
        M, natzero, ψ uN + 1, omega, (fun _ => univ (ψ uN)),
        ?_, ?_, hM, natzero_mem,
        fun _ _ => univ_mem_univ (ψ uN)⟩, enZ (ψ uN), ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV]
      · simp [interpExpr, Expr.instantiate1, updV, hfindZ', hvalZ',
          natZeroA, ConstantInfo.toConstantVal]
        try rfl
      intro z Az hAz hz
      have hAz' : Az = SetTheory.app M natzero := by
        simp [interpExpr, Expr.instantiate1, updV, hfindZ', hvalZ',
          natZeroA, ConstantInfo.toConstantVal,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hAz
        exact hAz.symm
      rw [hAz'] at hz
      refine ⟨?_, ?_⟩
      · -- the s-λ over the successor space
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨?_, en1U (ψ uN), ?_⟩
        · -- the successor space is annotation-truthful
          try simp only [AnnotOk]
          refine ⟨trivial,
            (if ψ uN = 0 then 0 else Nat.max (ψ uN) (ψ uN)), ?_⟩
          intro n An hAn hn
          have hAn' : An = omega := by
            simp [interpExpr, hfindN', hvalN', natA,
              ConstantInfo.toConstantVal,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hAn
            exact hAn.symm
          rw [hAn'] at hn
          refine ⟨?_, ?_⟩
          · -- the ih-∀ inside the successor space
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
              (by simp [Expr.instantiate1, AnnotOk]),
              M, n, ψ uN + 1, omega, (fun _ => univ (ψ uN)),
              ?_, ?_, hM, hn, fun _ _ => univ_mem_univ (ψ uN)⟩,
              ψ uN, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
            intro ih Aih hAih hih
            refine ⟨?_, ?_⟩
            · -- the body `motive (Nat.succ n)` of the ih-∀
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                ⟨(by simp [Expr.instantiate1, AnnotOk]),
                (by simp [Expr.instantiate1, AnnotOk]),
                natSuccVal V ψ, n, 1, omega, (fun _ => omega),
                ?_, ?_, natSuccVal_mem, hn, fun _ _ => omega_mem_univ⟩,
                M, SetTheory.app (natSuccVal V ψ) n,
                ψ uN + 1, omega, (fun _ => univ (ψ uN)),
                ?_, ?_, hM, ?_, fun _ _ => univ_mem_univ (ψ uN)⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · rw [natSuccVal_app hn]
                exact natsucc_mem hn
            · refine ⟨SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
                ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · exact hrawP M hM n hn
          · refine ⟨pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n), ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                hvalSc', natSuccA, ConstantInfo.toConstantVal,
                Level.eval, uN,
                -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              try rfl
            · by_cases hu : ψ uN = 0
              · rw [if_pos hu]
                exact hu ▸ hsfibP M hM n hn
              · rw [if_neg hu,
                  show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _]
                exact hsfibP M hM n hn
        · intro s As hAs hs
          have hAs' : As = pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n) := by
            simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
              hfindSc', hvalSc', natA, natSuccA,
              ConstantInfo.toConstantVal, Level.eval, uN, enUU,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              at hAs
            rw [← hAs]
            rfl
          rw [hAs'] at hs
          refine ⟨?_, ?_⟩
          · -- the n-λ over `Nat`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨trivial, ψ uN, ?_⟩
            intro n An hAn hn
            have hAn' : An = omega := by
              simp [interpExpr, hfindN', hvalN', natA,
                ConstantInfo.toConstantVal,
                -ite_eq_left_iff, -ite_eq_right_iff,
                -Nat.max_eq_zero_iff] at hAn
              exact hAn.symm
            rw [hAn'] at hn
            -- the recursor call chain memberships
            have h1 : SetTheory.app (natRecVal V ψ) M ∈ˢ
                pi (enZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
                  pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n' =>
                    pi (ψ uN) (SetTheory.app M n') fun _ =>
                      SetTheory.app M (SetTheory.app (natSuccVal V ψ) n'))
                    fun _ => pi (ψ uN) omega fun t => SetTheory.app M t :=
              app_mem hRecT hM (fun M' hM' => hzTP M' hM')
            have h2 : SetTheory.app (SetTheory.app (natRecVal V ψ) M) z ∈ˢ
                pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n' =>
                  pi (ψ uN) (SetTheory.app M n') fun _ =>
                    SetTheory.app M (SetTheory.app (natSuccVal V ψ) n'))
                  fun _ => pi (ψ uN) omega fun t => SetTheory.app M t :=
              app_mem h1 hz (fun _ _ => hs2P M hM)
            have h3 : SetTheory.app (SetTheory.app (SetTheory.app
                (natRecVal V ψ) M) z) s ∈ˢ
                pi (ψ uN) omega fun t => SetTheory.app M t :=
              app_mem h2 hs (fun _ _ => htTP M hM)
            have h4 : SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (natRecVal V ψ) M) z) s) n ∈ˢ
                SetTheory.app M n :=
              app_mem h3 hn (fun t ht => hMfib t ht)
            have hsn : SetTheory.app s n ∈ˢ
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n) :=
              app_mem hs hn (fun n' hn' => by
                try dsimp only
                rw [enUU_eq]
                by_cases hu : ψ uN = 0
                · rw [hu]
                  exact hu ▸ hsfibP M hM n' hn'
                · exact hsfibP M hM n' hn')
            refine ⟨?_, ?_⟩
            · -- the body `s n (Nat.rec motive z s n)`
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
                (by simp [Expr.instantiate1, AnnotOk]),
                s, n, enUU (ψ uN), omega,
                (fun n' => pi (ψ uN) (SetTheory.app M n') fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n')),
                ?_, ?_, hs, hn,
                (fun n' hn' => by
                  try dsimp only
                  rw [enUU_eq]
                  by_cases hu : ψ uN = 0
                  · rw [hu]
                    exact hu ▸ hsfibP M hM n' hn'
                  · exact hsfibP M hM n' hn')⟩,
                ⟨⟨⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                  natRecVal V ψ, M, enM (ψ uN),
                  pi (ψ uN + 1) omega (fun _ => univ (ψ uN)),
                  (fun M' => pi (enZ (ψ uN)) (SetTheory.app M' natzero)
                    fun _ => pi (en1U (ψ uN))
                      (pi (enUU (ψ uN)) omega fun n' =>
                        pi (ψ uN) (SetTheory.app M' n') fun _ =>
                          SetTheory.app M'
                            (SetTheory.app (natSuccVal V ψ) n'))
                      fun _ => pi (ψ uN) omega fun t =>
                        SetTheory.app M' t),
                  ?_, ?_, hRecT, hM, fun M' hM' => hzTP M' hM'⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                  SetTheory.app (natRecVal V ψ) M, z, enZ (ψ uN),
                  SetTheory.app M natzero,
                  (fun _ => pi (en1U (ψ uN))
                    (pi (enUU (ψ uN)) omega fun n' =>
                      pi (ψ uN) (SetTheory.app M n') fun _ =>
                        SetTheory.app M
                          (SetTheory.app (natSuccVal V ψ) n'))
                    fun _ => pi (ψ uN) omega fun t => SetTheory.app M t),
                  ?_, ?_, h1, hz, fun _ _ => hs2P M hM⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                  SetTheory.app (SetTheory.app (natRecVal V ψ) M) z, s,
                  en1U (ψ uN),
                  pi (enUU (ψ uN)) omega (fun n' =>
                    pi (ψ uN) (SetTheory.app M n') fun _ =>
                      SetTheory.app M (SetTheory.app (natSuccVal V ψ) n')),
                  (fun _ => pi (ψ uN) omega fun t => SetTheory.app M t),
                  ?_, ?_, h2, hs, fun _ _ => htTP M hM⟩,
                  (by simp [Expr.instantiate1, AnnotOk]),
                  SetTheory.app (SetTheory.app (SetTheory.app
                    (natRecVal V ψ) M) z) s, n, ψ uN, omega,
                  (fun t => SetTheory.app M t),
                  ?_, ?_, h3, hn, fun t ht => hMfib t ht⟩,
                SetTheory.app s n,
                SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n,
                ψ uN, SetTheory.app M n,
                (fun _ => SetTheory.app M
                  (SetTheory.app (natSuccVal V ψ) n)),
                ?_, ?_, hsn, h4, fun _ _ => hrawP M hM n hn⟩
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
            · -- n-cod slot
              refine ⟨SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n),
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
                ?_, ?_, ?_⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindR',
                  hvalR', natRecA, ConstantInfo.toConstantVal,
                  -ite_eq_left_iff, -ite_eq_right_iff,
                  -Nat.max_eq_zero_iff]
                try rfl
              · exact app_mem hsn h4 (fun _ _ => hrawP M hM n hn)
              · exact hrawP M hM n hn
          · -- s-cod slot
            refine ⟨SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n),
              pi (ψ uN) omega fun n =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
              ?_, ?_, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
                hfindR', hvalR', natA, natRecA,
                ConstantInfo.toConstantVal, Level.eval, uN,
                -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
              try rfl
            · refine lam_mem (V := V) (B := fun n =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
                fun n hn => ?_
              have hsn := app_mem hs hn (fun n' hn' => by
                try dsimp only
                rw [enUU_eq]
                by_cases hu : ψ uN = 0
                · rw [hu]
                  exact hu ▸ hsfibP M hM n' hn'
                · exact hsfibP M hM n' hn')
              have h4 := app_mem (app_mem (app_mem
                (app_mem hRecT hM (fun M' hM' => hzTP M' hM'))
                hz (fun _ _ => hs2P M hM))
                hs (fun _ _ => htTP M hM))
                hn (fun t ht => hMfib t ht)
              exact app_mem hsn h4 (fun _ _ => hrawP M hM n hn)
            · exact pi_mem_univ (u := 1) (v := ψ uN)
                (B := fun n => SetTheory.app M
                  (SetTheory.app (natSuccVal V ψ) n))
                omega_mem_univ (fun n hn => hrawP M hM n hn)
      · -- z-cod slot
        refine ⟨SetTheory.lam (en1U (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun s => SetTheory.lam (ψ uN) omega fun n =>
            SetTheory.app (SetTheory.app s n)
              (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (natRecVal V ψ) M) z) s) n),
          pi (en1U (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun n =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
          ?_, ?_, ?_⟩
        · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
            hfindR', hvalR', hfindSc', hvalSc', natA, natRecA, natSuccA,
            ConstantInfo.toConstantVal, Level.eval, uN, en1U, enUU,
            -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
          try rfl
        · refine lam_mem (V := V) (B := fun _ =>
            pi (ψ uN) omega fun n =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s hs => ?_
          refine lam_mem (V := V) (B := fun n =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun n hn => ?_
          have hsn := app_mem hs hn (fun n' hn' => by
            try dsimp only
            rw [enUU_eq]
            by_cases hu : ψ uN = 0
            · rw [hu]
              exact hu ▸ hsfibP M hM n' hn'
            · exact hsfibP M hM n' hn')
          have h4 := app_mem (app_mem (app_mem
            (app_mem hRecT hM (fun M' hM' => hzTP M' hM'))
            hz (fun _ _ => hs2P M hM))
            hs (fun _ _ => htTP M hM))
            hn (fun t ht => hMfib t ht)
          exact app_mem hsn h4 (fun _ _ => hrawP M hM n hn)
        · exact pi_mem_univ (u := en11UU (ψ uN)) (v := en1U (ψ uN))
            (hspP M hM)
            (fun _ _ => pi_mem_univ (u := 1) (v := ψ uN)
              (B := fun n => SetTheory.app M
                (SetTheory.app (natSuccVal V ψ) n))
              omega_mem_univ (fun n hn => hrawP M hM n hn))
    · -- motive-cod slot
      refine ⟨SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
        SetTheory.lam (en1U (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun s => SetTheory.lam (ψ uN) omega fun n =>
            SetTheory.app (SetTheory.app s n)
              (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (natRecVal V ψ) M) z) s) n),
        pi (enZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => pi (ψ uN) omega fun n =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
        ?_, ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
          hfindZ', hvalZ', hfindR', hvalR', hfindSc', hvalSc',
          natA, natZeroA, natRecA, natSuccA,
          ConstantInfo.toConstantVal, Level.eval, uN, enZ, en1U, en11UU, enUU,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
      · refine lam_mem (V := V) (B := fun _ =>
          pi (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => pi (ψ uN) omega fun n =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun z hz => ?_
        refine lam_mem (V := V) (B := fun _ =>
          pi (ψ uN) omega fun n =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun s hs => ?_
        refine lam_mem (V := V) (B := fun n =>
          SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          fun n hn => ?_
        have hsn := app_mem hs hn (fun n' hn' => by
          try dsimp only
          rw [enUU_eq]
          by_cases hu : ψ uN = 0
          · rw [hu]
            exact hu ▸ hsfibP M hM n' hn'
          · exact hsfibP M hM n' hn')
        have h4 := app_mem (app_mem (app_mem
          (app_mem hRecT hM (fun M' hM' => hzTP M' hM'))
          hz (fun _ _ => hs2P M hM))
          hs (fun _ _ => htTP M hM))
          hn (fun t ht => hMfib t ht)
        exact app_mem hsn h4 (fun _ _ => hrawP M hM n hn)
      · exact pi_mem_univ (u := ψ uN) (v := enZ (ψ uN))
          hMz
          (fun _ _ => pi_mem_univ (u := en11UU (ψ uN)) (v := en1U (ψ uN))
            (hspP M hM)
            (fun _ _ => pi_mem_univ (u := 1) (v := ψ uN)
              (B := fun n => SetTheory.app M
                (SetTheory.app (natSuccVal V ψ) n))
              omega_mem_univ (fun n hn => hrawP M hM n hn)))

end Setlec
