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
    rw [en1U_eq, enZ_eq]
    by_cases hu : ψ uN = 0
    · simp [hu]
    · rw [if_neg hu, if_neg (max_ne_zero_l (by decide : (1 : Nat) ≠ 0))]
      exact Nat.max_self _
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

theorem natFr_annotOk_tyM {cval : ConstVal V} :
    AnnotOk V cval env ψ 0 (rho0 V) natFrTyM := by
  simp only [natFrTyM, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro t A hA ht
  refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
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
  simp [interpExpr, Expr.instantiate1, updV, uN, enUU, hfindSc', hvalSc',
    natSuccA, ConstantInfo.toConstantVal, Level.substFn_nil, Level.eval,
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
    simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨⟨trivial, trivial, M, n, ψ uN + 1, omega,
      (fun _ => univ (ψ uN)),
      (by simp [interpExpr, updV]), (by simp [interpExpr, updV]),
      hM, hn, fun _ _ => univ_mem_univ _⟩, ⟨_, rfl⟩, ?_⟩
    intro ih Aih hAih hih
    refine ⟨?_, ?_⟩
    · -- the body `motive (Nat.succ n)`: nested app clauses
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
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
      simp only [Level.eval, show (Name.anonymous.str "u") = uN from rfl]
      have h := natFr_sfib hM n hn
      by_cases hu : ψ uN = 0
      · simpa [hu] using h
      · simpa [hu] using h

/-! ## The `RecRulesOk` clauses of the two rules -/

/-- The `RecRulesOk` clause of `Nat.rec`'s zero rule. -/
theorem natRecZero_ruleOk {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    (hfindR : env.find? (natName.str "rec") = some natRecA)
    (hvalR : ∀ ψ' : Name → Nat,
      cval (natName.str "rec") ψ' = natRecVal V ψ') :
    ∃ fvms bL,
      ruleLhsParts (natName.str "rec") natRecA.toConstantVal 3
        ((ConstantInfo.recRules natRecA).getD 0 default)
        natZeroA.toConstantVal = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = 3 +
        RecRule.nfields ((ConstantInfo.recRules natRecA).getD 0 default) ∧
      (closeLamsAt fvms bL).constsResolve env = true ∧
      ∀ ψ' : Name → Nat,
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' natRecZeroRhsA = some Rv := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") =
      some natZeroA := hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") =
      some natSuccA := hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' :=
    hvalSc
  have hfindR' : env.find? ((Name.anonymous.str "Nat").str "rec") =
      some natRecA := hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "rec") ψ' = natRecVal V ψ' :=
    hvalR
  have hparts : ruleLhsParts (natName.str "rec") natRecA.toConstantVal 3
      ((ConstantInfo.recRules natRecA).getD 0 default)
      natZeroA.toConstantVal = some
      ([(natFrM, ⟨.default, some (.imax (.param (Name.anonymous.str "u"))
          (.imax (.imax (.succ .zero)
            (.imax (.param (Name.anonymous.str "u"))
              (.param (Name.anonymous.str "u"))))
            (.param (Name.anonymous.str "u"))))⟩),
        (natFrZ, ⟨.default, some (.imax (.imax (.succ .zero)
          (.imax (.param (Name.anonymous.str "u"))
            (.param (Name.anonymous.str "u"))))
          (.param (Name.anonymous.str "u")))⟩),
        (natFrS, ⟨.default, some (.param (Name.anonymous.str "u"))⟩)],
       .app (.app (.app (.app natFrRec natFrM) natFrZ) natFrS)
         (.const ((Name.anonymous.str "Nat").str "zero") [])) := by rfl
  obtain ⟨hwf, hlen⟩ := ruleLhsParts_frameWf hparts rfl rfl rfl rfl
    (fun _ _ h => nomatch h)
  refine ⟨_, _, hparts, hwf, hlen, ?_, ?_⟩
  · exact ruleLhsParts_resolve hparts
      (by rw [hfindR]; rfl)
      (show (env.find? ((Name.anonymous.str "Nat").str "zero")).isSome = true
        by rw [hfindZ']; rfl)
      (by simp [ConstantInfo.toConstantVal, natRecA, Expr.constsResolve,
        hfindN', hfindZ', hfindSc'])
      (by simp [ConstantInfo.toConstantVal, natZeroA, Expr.constsResolve,
        hfindN'])
      (fun _ _ h => nomatch h)
  · intro ψ'
    have hAR : AnnotOk V cval env ψ' 0 (rho0 V) natRecZeroRhsA :=
      annotOk_natRecZero_rhs (cval := cval) (ψ := ψ') hfindN hvalN hfindZ
        hvalZ hfindSc hvalSc
    have hstep : ∀ {fvms : List (Expr × BinderMeta)} {bL : Expr},
        FrameWf 0 fvms bL →
        TowerOk (V := V) cval env ψ' 0 (rho0 V) fvms bL natRecZeroRhsA →
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' natRecZeroRhsA = some Rv := by
      intro fvms bL hwf' ht
      obtain ⟨⟨Rv, hL, hR⟩, hA⟩ := TowerOk.out ht hwf' hAR
      exact ⟨hA, Rv, hL, hR⟩
    refine hstep hwf ?_
    refine TowerOk.cons (A := pi (ψ' uN + 1) omega fun _ => univ (ψ' uN))
      (natFr_interp_tyM hfindN hvalN) (natFr_interp_tyM hfindN hvalN)
      (natFr_annotOk_tyM (V := V) (cval := cval)) ?_
    intro M hM
    have hMfib : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ' uN) :=
      fun k hk => app_mem hM hk (fun _ _ => univ_mem_univ (ψ' uN))
    refine TowerOk.cons (A := SetTheory.app M natzero)
      (natFr_interp_tyZ hfindZ hvalZ) (natFr_interp_tyZ hfindZ hvalZ)
      (natFr_annotOk_tyZ hfindZ hvalZ hM) ?_
    intro z hz
    refine TowerOk.cons (A := pi (enUU (ψ' uN)) omega fun n =>
        pi (ψ' uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (SetTheory.app (natSuccVal V ψ') n))
      (natFr_interp_tyS hfindN hvalN hfindSc hvalSc)
      (natFr_interp_tyS hfindN hvalN hfindSc hvalSc)
      (natFr_annotOk_tyS hfindN hvalN hfindSc hvalSc hM) ?_
    intro s hs
    have hs' : s ∈ˢ pi (ψ' uN) omega fun n =>
        pi (ψ' uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n) := natFr_Ssp_eq (V := V) (ψ := ψ') (M := M) ▸ hs
    -- the recursor value's membership in its interpreted type
    obtain ⟨T, hT, hmem⟩ := natRec_key (cval := cval) (env := env) (ψ := ψ')
      hfindN hvalN hfindZ hvalZ hfindSc hvalSc
    rw [interp_natRec_type hfindN hvalN hfindZ hvalZ hfindSc hvalSc] at hT
    obtain rfl := Option.some.inj hT
    -- the interpretation chain of the canonical lhs
    have hsub1 : Level.substFn ψ' [Name.anonymous.str "u"]
        [Level.param (Name.anonymous.str "u")] = ψ' :=
      funext fun _ => Level.substFn_map_param
    have hirec : interpExpr V cval env ψ' 3
        (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) natFrRec =
        some (natRecVal V ψ') := by
      simp only [natFrRec, interpExpr, hfindR', natRecA,
        ConstantInfo.toConstantVal, List.length_cons, List.length_nil,
        reduceIte, hsub1, hvalR']
    have hifvM : interpExpr V cval env ψ' 3
        (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) natFrM = some M := by
      simp [natFrM, interpExpr, updV]
    have hifvZ : interpExpr V cval env ψ' 3
        (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) natFrZ = some z := by
      simp [natFrZ, interpExpr, updV]
    have hifvS : interpExpr V cval env ψ' 3
        (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) natFrS = some s := by
      simp [natFrS, interpExpr, updV]
    have hizeroC : interpExpr V cval env ψ' 3
        (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s)
        (.const ((Name.anonymous.str "Nat").str "zero") []) =
        some natzero := by
      simp [interpExpr, hfindZ', hvalZ', natZeroA, ConstantInfo.toConstantVal]
    have hip1 : interpExpr V cval env ψ' 3
        (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s)
        (.app natFrRec natFrM) = some (SetTheory.app (natRecVal V ψ') M) := by
      rw [interpExpr, hirec, hifvM]
    have hip2 : interpExpr V cval env ψ' 3
        (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s)
        (.app (.app natFrRec natFrM) natFrZ) =
        some (SetTheory.app (SetTheory.app (natRecVal V ψ') M) z) := by
      rw [interpExpr, hip1, hifvZ]
    have hip3 : interpExpr V cval env ψ' 3
        (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s)
        (.app (.app (.app natFrRec natFrM) natFrZ) natFrS) =
        some (SetTheory.app (SetTheory.app (SetTheory.app (natRecVal V ψ') M)
          z) s) := by
      rw [interpExpr, hip2, hifvS]
    -- the membership chain along the tower
    have hm1 := app_mem hmem hM (fun M' hM' => natFr_T2_mem hM')
    have hm2 := app_mem hm1 hz (fun _ _ => natFr_T3_mem hM)
    have hm3 := app_mem hm2 hs (fun _ _ => natFr_T4_mem hM)
    refine TowerOk.nil (w := z) ?_ ?_ ?_
    · rw [interpExpr, hip3, hizeroC]
      show some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ') M) z) s) natzero) = some z
      rw [natRecVal_fold hM hz hs' natzero_mem, natrec_zero]
    · simp [Expr.instantiate1, interpExpr, updV]
    · simp only [AnnotOk, natFrRec, natFrM, natFrZ, natFrS]
      exact ⟨⟨⟨⟨trivial, trivial,
          natRecVal V ψ', M, enM (ψ' uN),
          pi (ψ' uN + 1) omega (fun _ => univ (ψ' uN)), _,
          hirec, hifvM, hmem, hM, fun M' hM' => natFr_T2_mem hM'⟩,
        trivial,
        SetTheory.app (natRecVal V ψ') M, z, enZ (ψ' uN),
          SetTheory.app M natzero, _,
          hip1, hifvZ, hm1, hz, fun _ _ => natFr_T3_mem hM⟩,
        trivial,
        SetTheory.app (SetTheory.app (natRecVal V ψ') M) z, s, en1U (ψ' uN),
          (pi (enUU (ψ' uN)) omega fun n =>
            pi (ψ' uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ') n)), _,
          hip2, hifvS, hm2, hs, fun _ _ => natFr_T4_mem hM⟩,
        trivial,
        SetTheory.app (SetTheory.app (SetTheory.app (natRecVal V ψ') M) z) s,
          natzero, ψ' uN, omega, (fun t => SetTheory.app M t),
          hip3, hizeroC, hm3, natzero_mem, fun t ht => hMfib t ht⟩

/-- The `RecRulesOk` clause of `Nat.rec`'s successor rule. -/
theorem natRecSucc_ruleOk {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    (hfindR : env.find? (natName.str "rec") = some natRecA)
    (hvalR : ∀ ψ' : Name → Nat,
      cval (natName.str "rec") ψ' = natRecVal V ψ') :
    ∃ fvms bL,
      ruleLhsParts (natName.str "rec") natRecA.toConstantVal 3
        ((ConstantInfo.recRules natRecA).getD 1 default)
        natSuccA.toConstantVal = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = 3 +
        RecRule.nfields ((ConstantInfo.recRules natRecA).getD 1 default) ∧
      (closeLamsAt fvms bL).constsResolve env = true ∧
      ∀ ψ' : Name → Nat,
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' natRecSuccRhsA = some Rv := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  have hfindZ' : env.find? ((Name.anonymous.str "Nat").str "zero") =
      some natZeroA := hfindZ
  have hvalZ' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "zero") ψ' = natzero := hvalZ
  have hfindSc' : env.find? ((Name.anonymous.str "Nat").str "succ") =
      some natSuccA := hfindSc
  have hvalSc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "succ") ψ' = natSuccVal V ψ' :=
    hvalSc
  have hfindR' : env.find? ((Name.anonymous.str "Nat").str "rec") =
      some natRecA := hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Nat").str "rec") ψ' = natRecVal V ψ' :=
    hvalR
  have hparts : ruleLhsParts (natName.str "rec") natRecA.toConstantVal 3
      ((ConstantInfo.recRules natRecA).getD 1 default)
      natSuccA.toConstantVal = some
      ([(natFrM, ⟨.default, some (.imax (.param (Name.anonymous.str "u"))
          (.imax (.imax (.succ .zero)
            (.imax (.param (Name.anonymous.str "u"))
              (.param (Name.anonymous.str "u"))))
            (.imax (.succ .zero) (.param (Name.anonymous.str "u")))))⟩),
        (natFrZ, ⟨.default, some (.imax (.imax (.succ .zero)
          (.imax (.param (Name.anonymous.str "u"))
            (.param (Name.anonymous.str "u"))))
          (.imax (.succ .zero) (.param (Name.anonymous.str "u"))))⟩),
        (natFrS, ⟨.default, some (.imax (.succ .zero)
          (.param (Name.anonymous.str "u")))⟩),
        (natFrN, ⟨.default, some (.param (Name.anonymous.str "u"))⟩)],
       .app (.app (.app (.app natFrRec natFrM) natFrZ) natFrS)
         (.app (.const ((Name.anonymous.str "Nat").str "succ") [])
           natFrN)) := by rfl
  obtain ⟨hwf, hlen⟩ := ruleLhsParts_frameWf hparts rfl rfl rfl rfl
    (fun _ _ h => nomatch h)
  refine ⟨_, _, hparts, hwf, hlen, ?_, ?_⟩
  · exact ruleLhsParts_resolve hparts
      (by rw [hfindR]; rfl)
      (show (env.find? ((Name.anonymous.str "Nat").str "succ")).isSome = true
        by rw [hfindSc']; rfl)
      (by simp [ConstantInfo.toConstantVal, natRecA, Expr.constsResolve,
        hfindN', hfindZ', hfindSc'])
      (by simp [ConstantInfo.toConstantVal, natSuccA, Expr.constsResolve,
        hfindN'])
      (fun _ _ h => nomatch h)
  · intro ψ'
    have hAR : AnnotOk V cval env ψ' 0 (rho0 V) natRecSuccRhsA :=
      annotOk_natRecSucc_rhs (cval := cval) (ψ := ψ') hfindN hvalN hfindZ
        hvalZ hfindSc hvalSc hfindR hvalR
    have hstep : ∀ {fvms : List (Expr × BinderMeta)} {bL : Expr},
        FrameWf 0 fvms bL →
        TowerOk (V := V) cval env ψ' 0 (rho0 V) fvms bL natRecSuccRhsA →
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' natRecSuccRhsA = some Rv := by
      intro fvms bL hwf' ht
      obtain ⟨⟨Rv, hL, hR⟩, hA⟩ := TowerOk.out ht hwf' hAR
      exact ⟨hA, Rv, hL, hR⟩
    refine hstep hwf ?_
    refine TowerOk.cons (A := pi (ψ' uN + 1) omega fun _ => univ (ψ' uN))
      (natFr_interp_tyM hfindN hvalN) (natFr_interp_tyM hfindN hvalN)
      (natFr_annotOk_tyM (V := V) (cval := cval)) ?_
    intro M hM
    have hMfib : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ' uN) :=
      fun k hk => app_mem hM hk (fun _ _ => univ_mem_univ (ψ' uN))
    refine TowerOk.cons (A := SetTheory.app M natzero)
      (natFr_interp_tyZ hfindZ hvalZ) (natFr_interp_tyZ hfindZ hvalZ)
      (natFr_annotOk_tyZ hfindZ hvalZ hM) ?_
    intro z hz
    refine TowerOk.cons (A := pi (enUU (ψ' uN)) omega fun n =>
        pi (ψ' uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (SetTheory.app (natSuccVal V ψ') n))
      (natFr_interp_tyS hfindN hvalN hfindSc hvalSc)
      (natFr_interp_tyS hfindN hvalN hfindSc hvalSc)
      (natFr_annotOk_tyS hfindN hvalN hfindSc hvalSc hM) ?_
    intro s hs
    have hs' : s ∈ˢ pi (ψ' uN) omega fun n =>
        pi (ψ' uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n) := natFr_Ssp_eq (V := V) (ψ := ψ') (M := M) ▸ hs
    have hityN : interpExpr V cval env ψ' 3
        (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s)
        (.const (Name.anonymous.str "Nat") []) = some omega := by
      simp [interpExpr, hfindN', hvalN', natA, ConstantInfo.toConstantVal]
    refine TowerOk.cons (A := omega) hityN hityN (by simp [AnnotOk]) ?_
    intro n hn
    -- the recursor value's membership in its interpreted type
    obtain ⟨T, hT, hmem⟩ := natRec_key (cval := cval) (env := env) (ψ := ψ')
      hfindN hvalN hfindZ hvalZ hfindSc hvalSc
    rw [interp_natRec_type hfindN hvalN hfindZ hvalZ hfindSc hvalSc] at hT
    obtain rfl := Option.some.inj hT
    have hsub1 : Level.substFn ψ' [Name.anonymous.str "u"]
        [Level.param (Name.anonymous.str "u")] = ψ' :=
      funext fun _ => Level.substFn_map_param
    have hirec : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
        natFrRec = some (natRecVal V ψ') := by
      simp only [natFrRec, interpExpr, hfindR', natRecA,
        ConstantInfo.toConstantVal, List.length_cons, List.length_nil,
        reduceIte, hsub1, hvalR']
    have hifvM : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
        natFrM = some M := by
      simp [natFrM, interpExpr, updV]
    have hifvZ : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
        natFrZ = some z := by
      simp [natFrZ, interpExpr, updV]
    have hifvS : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
        natFrS = some s := by
      simp [natFrS, interpExpr, updV]
    have hifvN : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
        natFrN = some n := by
      simp [natFrN, interpExpr, updV]
    have hisuccC : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
        (.const ((Name.anonymous.str "Nat").str "succ") []) =
        some (natSuccVal V ψ') := by
      simp [interpExpr, hfindSc', hvalSc', natSuccA,
        ConstantInfo.toConstantVal, Level.substFn_nil]
    have hisuccN : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
        (.app (.const ((Name.anonymous.str "Nat").str "succ") []) natFrN) =
        some (SetTheory.app (natSuccVal V ψ') n) := by
      rw [interpExpr, hisuccC, hifvN]
    have hip1 : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
        (.app natFrRec natFrM) = some (SetTheory.app (natRecVal V ψ') M) := by
      rw [interpExpr, hirec, hifvM]
    have hip2 : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
        (.app (.app natFrRec natFrM) natFrZ) =
        some (SetTheory.app (SetTheory.app (natRecVal V ψ') M) z) := by
      rw [interpExpr, hip1, hifvZ]
    have hip3 : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
        (.app (.app (.app natFrRec natFrM) natFrZ) natFrS) =
        some (SetTheory.app (SetTheory.app (SetTheory.app (natRecVal V ψ') M)
          z) s) := by
      rw [interpExpr, hip2, hifvS]
    have hm1 := app_mem hmem hM (fun M' hM' => natFr_T2_mem hM')
    have hm2 := app_mem hm1 hz (fun _ _ => natFr_T3_mem hM)
    have hm3 := app_mem hm2 hs (fun _ _ => natFr_T4_mem hM)
    have hsuccN_mem : SetTheory.app (natSuccVal V ψ') n ∈ˢ omega := by
      rw [natSuccVal_app hn]
      exact natsucc_mem hn
    refine TowerOk.nil
      (w := SetTheory.app (SetTheory.app s n) (natrec z s n)) ?_ ?_ ?_
    · rw [interpExpr, hip3, hisuccN]
      show some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ') M) z) s) (SetTheory.app (natSuccVal V ψ') n)) =
        some (SetTheory.app (SetTheory.app s n) (natrec z s n))
      rw [natSuccVal_app hn,
        natRecVal_fold hM hz hs' (natsucc_mem hn), natrec_succ z s hn]
    · -- the opened rhs bottom: `succ n (Nat.rec motive zero succ n)`
      show interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
        (.app (.app natFrS natFrN)
          (.app (.app (.app (.app natFrRec natFrM) natFrZ) natFrS) natFrN)) =
        some (SetTheory.app (SetTheory.app s n) (natrec z s n))
      have houter : interpExpr V cval env ψ' 4
          (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
          (.app natFrS natFrN) = some (SetTheory.app s n) := by
        rw [interpExpr, hifvS, hifvN]
      have hinner : interpExpr V cval env ψ' 4
          (updV V (updV V (updV V (updV V (rho0 V) 0 M) 1 z) 2 s) 3 n)
          (.app (.app (.app (.app natFrRec natFrM) natFrZ) natFrS) natFrN) =
          some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
            (natRecVal V ψ') M) z) s) n) := by
        rw [interpExpr, hip3, hifvN]
      rw [interpExpr, houter, hinner]
      show some (SetTheory.app (SetTheory.app s n) (SetTheory.app
        (SetTheory.app (SetTheory.app (SetTheory.app (natRecVal V ψ') M) z)
          s) n)) = _
      rw [natRecVal_fold hM hz hs' hn]
    · simp only [AnnotOk, natFrRec, natFrM, natFrZ, natFrS, natFrN]
      exact ⟨⟨⟨⟨trivial, trivial,
          natRecVal V ψ', M, enM (ψ' uN),
          pi (ψ' uN + 1) omega (fun _ => univ (ψ' uN)), _,
          hirec, hifvM, hmem, hM, fun M' hM' => natFr_T2_mem hM'⟩,
        trivial,
        SetTheory.app (natRecVal V ψ') M, z, enZ (ψ' uN),
          SetTheory.app M natzero, _,
          hip1, hifvZ, hm1, hz, fun _ _ => natFr_T3_mem hM⟩,
        trivial,
        SetTheory.app (SetTheory.app (natRecVal V ψ') M) z, s, en1U (ψ' uN),
          (pi (enUU (ψ' uN)) omega fun n' =>
            pi (ψ' uN) (SetTheory.app M n') fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ') n')), _,
          hip2, hifvS, hm2, hs, fun _ _ => natFr_T4_mem hM⟩,
        ⟨trivial, trivial,
          natSuccVal V ψ', n, 1, omega, (fun _ => omega),
          hisuccC, hifvN, natSuccVal_mem, hn, fun _ _ => omega_mem_univ⟩,
        SetTheory.app (SetTheory.app (SetTheory.app (natRecVal V ψ') M) z) s,
          SetTheory.app (natSuccVal V ψ') n, ψ' uN, omega,
          (fun t => SetTheory.app M t),
          hip3, hisuccN, hm3, hsuccN_mem, fun t ht => hMfib t ht⟩

end Setlec
