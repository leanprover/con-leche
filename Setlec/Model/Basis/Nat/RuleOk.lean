import Setlec.Model.Basis.Nat.AnnotOk
import Setlec.Model.RuleFold

/-!
# `Nat.rec`: the total λ-equality clauses of `RecRulesOk`

Per stored rule, the canonical iota left-hand side (`ruleLhsParts` on
the pinned data) is a well-formed λ-tower that interprets, for every
level assignment, to the same set as the stored right-hand side
(assembled through `TowerOk.out`); the fold equations are the
value-level `natrec_zero`/`natrec_succ`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-! ## The canonical frame components (computed from the pinned data) -/

/-- The motive annotation of the canonical `Nat.rec` frames. -/
def natFrTyM : Expr :=
  .forallE (Name.anonymous.str "t") (.const (Name.anonymous.str "Nat") [])
    (.sort (.param (Name.anonymous.str "u")))
    ⟨.default, some (.succ (.param (Name.anonymous.str "u")))⟩

/-- The motive frame variable. -/
def natFrM : Expr := .fvar 0 (Name.anonymous.str "motive") natFrTyM

/-- The zero minor-premise annotation. -/
def natFrTyZ : Expr :=
  .app natFrM (.const ((Name.anonymous.str "Nat").str "zero") [])

/-- The zero minor-premise frame variable. -/
def natFrZ : Expr := .fvar 1 (Name.anonymous.str "zero") natFrTyZ

/-- The successor minor-premise annotation. -/
def natFrTyS : Expr :=
  .forallE (Name.anonymous.str "n") (.const (Name.anonymous.str "Nat") [])
    (.forallE (Name.anonymous.str "n_ih") (.app natFrM (.bvar 0))
      (.app natFrM (.app (.const ((Name.anonymous.str "Nat").str "succ") [])
        (.bvar 1)))
      ⟨.default, some (.param (Name.anonymous.str "u"))⟩)
    ⟨.default, some (.imax (.param (Name.anonymous.str "u"))
      (.param (Name.anonymous.str "u")))⟩

/-- The successor minor-premise frame variable. -/
def natFrS : Expr := .fvar 2 (Name.anonymous.str "succ") natFrTyS

/-- The field frame variable of the successor rule. -/
def natFrN : Expr :=
  .fvar 3 (Name.anonymous.str "n") (.const (Name.anonymous.str "Nat") [])

/-- The recursor head of the canonical left-hand sides. -/
def natFrRec : Expr :=
  .const ((Name.anonymous.str "Nat").str "rec")
    [.param (Name.anonymous.str "u")]

/-! ## Stage facts: interpretation and truthfulness of the frame
annotations -/

theorem natFr_interp_tyM {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega) :
    interpExpr V cval env ψ 0 (rho0 V) natFrTyM =
      some (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  simp only [natFrTyM, interpExpr, hfindN', hvalN', natA,
    ConstantInfo.toConstantVal, List.length_nil, reduceIte, Level.eval,
    Level.substFn]
  simp [interpExpr, Expr.instantiate1, updV, uN]
  rfl

theorem natFr_annotOk_tyM {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega) :
    AnnotOk V cval env ψ 0 (rho0 V) natFrTyM := by
  simp only [natFrTyM, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro t A hA ht
  refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
  intro v hv
  obtain rfl := Option.some.inj hv
  refine ⟨univ (ψ uN), ?_, ?_⟩
  · simp [Expr.instantiate1, interpExpr, Level.eval, uN]
  · exact univ_mem_univ (ψ uN)

theorem natFr_interp_tyZ {cval : ConstVal V} {M : V}
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero) :
    interpExpr V cval env ψ 1 (updV V (rho0 V) 0 M) natFrTyZ =
      some (SetTheory.app M natzero) := by
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") =
      some natZeroA := hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  simp [natFrTyZ, natFrM, interpExpr, updV, hfindZ', hvalZ', natZeroA,
    ConstantInfo.toConstantVal]

theorem natFr_annotOk_tyZ {cval : ConstVal V} {M : V}
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hM : M ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN)) :
    AnnotOk V cval env ψ 1 (updV V (rho0 V) 0 M) natFrTyZ := by
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") =
      some natZeroA := hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  simp only [natFrTyZ, natFrM, AnnotOk]
  exact ⟨trivial, trivial, M, natzero, ψ uN + 1, omega,
    (fun _ => univ (ψ uN)),
    (by simp [interpExpr, updV]),
    (by simp [interpExpr, hfindZ', hvalZ', natZeroA,
      ConstantInfo.toConstantVal]),
    hM, natzero_mem, fun _ _ => univ_mem_univ _⟩

theorem natFr_interp_tyS {cval : ConstVal V} {M z : V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ') :
    interpExpr V cval env ψ 2 (updV V (updV V (rho0 V) 0 M) 1 z) natFrTyS =
      some (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") =
      some natSuccA := hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' :=
    hvalSc
  simp only [natFrTyS, natFrM, natFrTyM, interpExpr, hfindN', hvalN',
    hfindSc', hvalSc', natA, natSuccA, ConstantInfo.toConstantVal,
    List.length_nil, List.length_cons, reduceIte, Level.eval, Level.substFn]
  simp [interpExpr, Expr.instantiate1, updV, uN, enUU,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

theorem natFr_annotOk_tyS {cval : ConstVal V} {M z : V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    (hM : M ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN)) :
    AnnotOk V cval env ψ 2 (updV V (updV V (rho0 V) 0 M) 1 z) natFrTyS := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") =
      some natSuccA := hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' :=
    hvalSc
  have hMfib : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
    fun k hk => app_mem hM hk (fun _ _ => univ_mem_univ (ψ uN))
  simp only [natFrTyS, natFrM, natFrTyM, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro n An hAn hn
  have hAn' : An = omega := by
    simp only [interpExpr, hfindN', hvalN', natA, ConstantInfo.toConstantVal,
      List.length_nil, reduceIte] at hAn
    exact (Option.some.inj hAn).symm
  subst hAn'
  refine ⟨?_, ?_⟩
  · -- the opened `∀ (n_ih : motive n), motive (Nat.succ n)`
    simp only [Expr.instantiate1, AnnotOk]
    refine ⟨⟨trivial, trivial, M, n, ψ uN + 1, omega,
      (fun _ => univ (ψ uN)),
      (by simp [interpExpr, updV]), (by simp [interpExpr, updV]),
      hM, hn, fun _ _ => univ_mem_univ _⟩, ⟨_, rfl⟩, ?_⟩
    intro ih Aih hAih hih
    refine ⟨?_, ?_⟩
    · -- the body `motive (Nat.succ n)`: nested app clauses
      simp only [Expr.instantiate1, AnnotOk]
      refine ⟨trivial,
        ⟨trivial, trivial, natSuccVal V ψ, n, 1, omega, (fun _ => omega),
          (by simp [interpExpr, hfindSc', hvalSc', natSuccA,
            ConstantInfo.toConstantVal, Level.substFn_nil]),
          (by simp [interpExpr, updV]),
          natSuccVal_mem, hn, fun _ _ => omega_mem_univ⟩,
        M, SetTheory.app (natSuccVal V ψ) n, ψ uN + 1, omega,
        (fun _ => univ (ψ uN)),
        (by simp [interpExpr, updV]),
        ?_, hM, ?_, fun _ _ => univ_mem_univ _⟩
      · rw [interpExpr]
        simp [interpExpr, updV, hfindSc', hvalSc', natSuccA,
          ConstantInfo.toConstantVal, Level.substFn_nil]
      · rw [natSuccVal_app hn]
        exact natsucc_mem hn
    · intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨SetTheory.app M (SetTheory.app (natSuccVal V ψ) n), ?_, ?_⟩
      · rw [interpExpr]
        simp [interpExpr, updV, hfindSc', hvalSc', natSuccA,
          ConstantInfo.toConstantVal, Level.substFn_nil]
      · rw [natSuccVal_app hn]
        exact hMfib (natsucc n) (natsucc_mem hn)
  · intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨pi (ψ uN) (SetTheory.app M n)
      (fun _ => SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindSc', hvalSc', natSuccA,
        ConstantInfo.toConstantVal, Level.eval, uN, Level.substFn_nil,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · have heq : (pi (ψ uN) (SetTheory.app M n)
          fun _ => SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
          (pi (ψ uN) (SetTheory.app M n)
            fun _ => SetTheory.app M (natsucc n)) :=
        pi_congr fun _ _ => by rw [natSuccVal_app hn]
      rw [heq]
      simp only [Level.eval]
      exact natFr_sfib_aux hMfib n hn
where
  natFr_sfib_aux {M : V}
      (hMfib : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN))
      (n : V) (hn : n ∈ˢ omega) :
      (pi (ψ uN) (SetTheory.app M n) fun _ =>
        SetTheory.app M (natsucc n)) ∈ˢ univ (ψ (Name.anonymous.str "u")) := by
    have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib n hn)
      (fun _ _ => hMfib (natsucc n) (natsucc_mem hn))
    by_cases hu : ψ uN = 0
    · simpa [uN, hu] using this
    · simpa [uN, hu, Nat.max_self] using this

/-! ## Membership facts along the recursor's interpreted type -/

/-- The raw successor minor-premise space folds to the `natsucc` one. -/
theorem natFr_Ssp_eq {M : V} :
    (pi (enUU (ψ uN)) omega fun n =>
      pi (ψ uN) (SetTheory.app M n) fun _ =>
        SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
    (pi (ψ uN) omega fun n =>
      pi (ψ uN) (SetTheory.app M n) fun _ =>
        SetTheory.app M (natsucc n)) := by
  rw [enUU_eq]
  exact pi_congr fun n hn => pi_congr fun _ _ => by rw [natSuccVal_app hn]

theorem natFr_sfib {M : V}
    (hM : M ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN)) :
    ∀ n, n ∈ˢ omega → (pi (ψ uN) (SetTheory.app M n) fun _ =>
      SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
  intro n hn
  have hMfib : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
    fun k hk => app_mem hM hk (fun _ _ => univ_mem_univ (ψ uN))
  have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib n hn)
    (fun _ _ => hMfib (natsucc n) (natsucc_mem hn))
  by_cases hu : ψ uN = 0
  · simpa [hu] using this
  · simpa [hu, Nat.max_self] using this

theorem natFr_Ssp_mem {M : V}
    (hM : M ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN)) :
    (pi (enUU (ψ uN)) omega fun n =>
      pi (ψ uN) (SetTheory.app M n) fun _ =>
        SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
      univ (en1U (ψ uN)) := by
  rw [natFr_Ssp_eq, en1U_eq]
  exact pi_mem_univ (u := 1) (v := ψ uN) (omega_mem_univ (V := V))
    (natFr_sfib hM)

theorem natFr_T4_mem {M : V}
    (hM : M ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN)) :
    (pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
      univ (en1U (ψ uN)) := by
  rw [en1U_eq]
  exact pi_mem_univ (u := 1) (v := ψ uN) (omega_mem_univ (V := V))
    (fun t ht => app_mem hM ht (fun _ _ => univ_mem_univ _))

theorem natFr_T3_mem {M : V}
    (hM : M ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN)) :
    (pi (en1U (ψ uN))
      (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
      fun _ => pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
      univ (enZ (ψ uN)) := by
  have h := pi_mem_univ (u := en1U (ψ uN)) (v := en1U (ψ uN))
    (natFr_Ssp_mem hM) (fun _ _ => natFr_T4_mem hM)
  have hcc : (if en1U (ψ uN) = 0 then 0
      else Nat.max (en1U (ψ uN)) (en1U (ψ uN))) = enZ (ψ uN) := by
    rw [Nat.max_self, en1U_eq, enZ_eq]
    by_cases hu : ψ uN = 0
    · simp [hu]
    · rw [if_neg hu, if_neg hu,
        if_neg (max_ne_zero_l (by decide : (1 : Nat) ≠ 0))]
  rw [hcc] at h
  exact h

theorem natFr_T2_mem {M : V}
    (hM : M ∈ˢ pi (ψ uN + 1) omega fun _ => univ (ψ uN)) :
    (pi (enZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
      pi (en1U (ψ uN))
        (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
        fun _ => pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
      univ (enM (ψ uN)) :=
  pi_mem_univ (u := ψ uN) (v := enZ (ψ uN))
    (app_mem hM natzero_mem (fun _ _ => univ_mem_univ _))
    (fun _ _ => natFr_T3_mem hM)

end Setlec
