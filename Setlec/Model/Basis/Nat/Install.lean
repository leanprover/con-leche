import Setlec.Model.Basis.Util

/-!
# `Nat` basis block: interpretation and `hkey` obligations
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-! ## The `Nat` basis block -/

/-- Interpretation of `Nat`'s pinned type (`Type`). -/
theorem interp_nat_type {cval : ConstVal V} :
    interpClosed V cval env ψ natA.toConstantVal.type = some (univ 1) := by
  simp [interpClosed, natA, ConstantInfo.toConstantVal, interpExpr, Level.eval]

/-- `Nat`'s value inhabits its type. -/
theorem nat_key {cval : ConstVal V} :
    ∃ T, interpClosed V cval env ψ natA.toConstantVal.type = some T ∧
      (omega : V) ∈ˢ T :=
  ⟨univ 1, interp_nat_type, omega_mem_univ⟩

/-- `Nat.zero`'s value inhabits its type. -/
theorem natZero_key {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega) :
    ∃ T, interpClosed V cval env ψ natZeroA.toConstantVal.type = some T ∧
      (natzero : V) ∈ˢ T := by
  refine ⟨omega, ?_, natzero_mem⟩
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  simp [interpClosed, natZeroA, ConstantInfo.toConstantVal, interpExpr,
    hfindN', hvalN', natA]

/-- `Nat.succ`'s value is a member of its pi-type. -/
theorem natSuccVal_mem :
    (natSuccVal V ψ : V) ∈ˢ pi 1 omega (fun _ => omega) := by
  simp only [natSuccVal]
  exact lam_mem (V := V) (B := fun _ => omega) fun n hn => natsucc_mem hn

/-- Applying `Nat.succ`'s value computes to the successor. -/
theorem natSuccVal_app {n : V} (hn : n ∈ˢ omega) :
    SetTheory.app (natSuccVal V ψ) n = natsucc n := by
  simp only [natSuccVal]
  exact app_lam (B := fun _ => omega) hn (fun k hk => natsucc_mem hk)
    (fun _ _ => omega_mem_univ)

/-- Interpretation of `Nat.succ`'s pinned type, computed. -/
theorem interp_natSucc_type {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega) :
    interpClosed V cval env ψ natSuccA.toConstantVal.type =
      some (pi 1 omega fun _ => omega) := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  simp only [interpClosed, natSuccA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD, hfindN', hvalN', natA,
    List.length_nil, reduceIte]
  try simp [interpExpr, Expr.instantiate1, updV]
  try rfl

/-- `Nat.succ`'s value inhabits its type. -/
theorem natSucc_key {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega) :
    ∃ T, interpClosed V cval env ψ natSuccA.toConstantVal.type = some T ∧
      natSuccVal V ψ ∈ˢ T :=
  ⟨_, interp_natSucc_type hfindN hvalN, natSuccVal_mem⟩

/-- `Nat.succ`'s type carries truthful annotations. -/
theorem annotOk_natSucc_type {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega) :
    AnnotOk V cval env ψ 0 (rho0 V) natSuccA.toConstantVal.type := by
  have hfindN' : env.find? (Name.anonymous.str "Nat") = some natA := hfindN
  have hvalN' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Nat") ψ' = omega := hvalN
  simp only [natSuccA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨trivial, ?_⟩
  intro n Sn hSn hnmem
  refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
  refine ⟨omega, ?_⟩
  simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN', natA,
    ConstantInfo.toConstantVal]

/-! Raw evaluations of `Nat.rec`'s binder annotations. -/

def enUU (u : Nat) : Nat := if u = 0 then 0 else u
def en1U (u : Nat) : Nat := if u = 0 then 0 else Nat.max 1 u
def en11UU (u : Nat) : Nat :=
  if enUU u = 0 then 0 else Nat.max 1 (enUU u)
def enZ (u : Nat) : Nat :=
  if en1U u = 0 then 0 else Nat.max (en11UU u) (en1U u)
def enM (u : Nat) : Nat :=
  if enZ u = 0 then 0 else Nat.max u (enZ u)

theorem enUU_eq (u : Nat) : enUU u = u := by
  unfold enUU
  by_cases h : u = 0
  · rw [if_pos h, h]
  · rw [if_neg h]

theorem en1U_eq (u : Nat) :
    en1U u = if u = 0 then 0 else Nat.max 1 u := rfl

theorem en11UU_eq (u : Nat) :
    en11UU u = if u = 0 then 0 else Nat.max 1 u := by
  unfold en11UU
  rw [enUU_eq]

theorem enZ_eq (u : Nat) :
    enZ u = if u = 0 then 0 else Nat.max 1 u := by
  unfold enZ
  rw [en11UU_eq, en1U_eq]
  by_cases h : u = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_l (by decide) : Nat.max 1 u ≠ 0)]
    exact Nat.max_self _

theorem enM_eq (u : Nat) :
    enM u = if u = 0 then 0 else Nat.max 1 u := by
  unfold enM
  rw [enZ_eq]
  by_cases h : u = 0
  · simp [h]
  · simp only [if_neg h]
    rw [if_neg (max_ne_zero_l (by decide) : Nat.max 1 u ≠ 0)]
    exact Nat.le_antisymm
      (Nat.max_le.mpr ⟨Nat.le_max_right 1 u, Nat.le_refl _⟩)
      (Nat.le_max_right _ _)


/-- Interpretation of `Nat.rec`'s pinned type, computed. -/
theorem interp_natRec_type {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ') :
    interpClosed V cval env ψ natRecA.toConstantVal.type =
      some (pi (enM (ψ uN)) (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        pi (enZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M t) := by
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
  simp only [interpClosed, natRecA, ConstantInfo.toConstantVal, interpExpr,
    Expr.instantiate1, updV, Level.eval, Option.getD,
    hfindN', hvalN', hfindZ', hvalZ', hfindSc', hvalSc', natA, natZeroA,
    natSuccA, List.length_cons, List.length_nil, reduceIte, Level.substFn]
  simp [interpExpr, updV, Expr.instantiate1, uN,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

/-- `Nat.rec`'s value inhabits its type (`natrec_mem`). -/
theorem natRec_key {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ') :
    ∃ T, interpClosed V cval env ψ natRecA.toConstantVal.type = some T ∧
      natRecVal V ψ ∈ˢ T := by
  refine ⟨_, interp_natRec_type hfindN hvalN hfindZ hvalZ hfindSc hvalSc, ?_⟩
  rw [enM_eq, enZ_eq, en1U_eq, enUU_eq]
  simp only [natRecVal]
  refine lam_mem (V := V) fun M hM => ?_
  refine lam_mem (V := V) fun z hz => ?_
  have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app M n ∈ˢ univ (ψ uN) :=
    fun n hn => app_mem hM hn (fun _ _ => univ_mem_univ (ψ uN))
  have hSuccSp : (pi (ψ uN) omega fun n =>
      pi (ψ uN) (SetTheory.app M n) fun _ =>
        SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
      (pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) :=
    pi_congr fun n hn => by rw [natSuccVal_app hn]
  rw [hSuccSp]
  refine lam_mem (V := V) fun s hs => ?_
  refine lam_mem (V := V) fun t ht => ?_
  have hsfib : ∀ n, n ∈ˢ omega →
      (pi (ψ uN) (SetTheory.app M n) fun _ =>
        SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
    intro n hn
    have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib n hn)
      (fun _ _ => hMfib (natsucc n) (natsucc_mem hn))
    by_cases hu : ψ uN = 0
    · simpa [hu] using this
    · simpa [hu, Nat.max_self] using this
  refine natrec_mem hz ?_ ht
  intro k hk ih hih
  have h1 : SetTheory.app s k ∈ˢ pi (ψ uN) (SetTheory.app M k)
      (fun _ => SetTheory.app M (natsucc k)) :=
    app_mem hs hk hsfib
  exact app_mem h1 hih (fun _ _ => hMfib (natsucc k) (natsucc_mem hk))

/-- `Nat.rec`'s type carries truthful annotations. -/
theorem annotOk_natRec_type {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ') :
    AnnotOk V cval env ψ 0 (rho0 V) natRecA.toConstantVal.type := by
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
  simp only [natRecA, ConstantInfo.toConstantVal, AnnotOk]
  refine ⟨?_, ?_⟩
  · -- the motive space `(t : Nat) → Sort u`
    try simp only [AnnotOk]
    refine ⟨trivial, ?_⟩
    intro t St hSt htmem
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
    refine ⟨univ (ψ uN), ?_⟩
    simp [interpExpr, Expr.instantiate1, updV, Level.eval, uN]
  · intro M SM hSM hMmem
    simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN', natA,
      ConstantInfo.toConstantVal, Level.eval, uN,
      -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSM
    subst hSM
    have hMmem' : M ∈ˢ pi (ψ uN + 1) omega (fun _ => univ (ψ uN)) := hMmem
    have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app M n ∈ˢ univ (ψ uN) :=
      fun n hn => app_mem hMmem' hn (fun _ _ => univ_mem_univ (ψ uN))
    refine ⟨?_, ?_⟩
    · -- opened `∀ (zero : motive Nat.zero), …`
      try simp only [Expr.instantiate1, reduceIte, AnnotOk]
      refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
        (by simp [Expr.instantiate1, AnnotOk]),
        M, natzero, omega, (fun _ => univ (ψ uN)),
        ?_, ?_, hMmem', natzero_mem⟩, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV]
      · simp [interpExpr, Expr.instantiate1, updV, hfindZ', hvalZ',
          natZeroA, ConstantInfo.toConstantVal]
      intro z Sz hSz hzmem
      refine ⟨?_, ?_⟩
      · -- opened `∀ (succ : …), …`
        try simp only [Expr.instantiate1, reduceIte, AnnotOk]
        refine ⟨?_, ?_⟩
        · -- the successor minor-premise space
          try simp only [Expr.instantiate1, reduceIte, AnnotOk]
          refine ⟨trivial, ?_⟩
          intro n Sn hSn hnmem
          simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN', natA,
            ConstantInfo.toConstantVal] at hSn
          subst hSn
          refine ⟨?_, ?_⟩
          · -- opened `∀ (n_ih : motive n), motive (Nat.succ n)`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
              (by simp [Expr.instantiate1, AnnotOk]),
              M, n, omega, (fun _ => univ (ψ uN)),
              ?_, ?_, hMmem', hnmem⟩, ?_⟩
            · simp [interpExpr, Expr.instantiate1, updV]
            · simp [interpExpr, Expr.instantiate1, updV]
            intro ih Sih hSih hihmem
            refine ⟨?_, ?_⟩
            · -- the body `motive (Nat.succ n)`
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                ⟨⟨trivial, (by simp [Expr.instantiate1, AnnotOk]),
                  natSuccVal V ψ, n, omega, (fun _ => omega),
                  ?_, ?_, natSuccVal_mem, hnmem⟩,
                M, SetTheory.app (natSuccVal V ψ) n,
                omega, (fun _ => univ (ψ uN)),
                ?_, ?_, hMmem', ?_⟩⟩
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal]
                try rfl
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                  hvalSc', natSuccA, ConstantInfo.toConstantVal]
                try rfl
              · rw [natSuccVal_app hnmem]
                exact natsucc_mem hnmem
            · -- interpretability of the body
              refine ⟨SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
                ?_⟩
              simp [interpExpr, Expr.instantiate1, updV, hfindSc',
                hvalSc', natSuccA, ConstantInfo.toConstantVal]
              try rfl
          · -- interpretability of the opened body
            refine ⟨pi (ψ uN) (SetTheory.app M n) (fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)), ?_⟩
            simp [interpExpr, Expr.instantiate1, updV, hfindSc',
              hvalSc', natSuccA, ConstantInfo.toConstantVal, Level.eval, uN,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl
        · intro s Ss hSs hsmem
          refine ⟨?_, ?_⟩
          · -- opened `∀ (t : Nat), motive t`
            try simp only [Expr.instantiate1, reduceIte, AnnotOk]
            refine ⟨trivial, ?_⟩
            intro t St hSt htmem
            simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN', natA,
              ConstantInfo.toConstantVal] at hSt
            subst hSt
            refine ⟨?_, ?_⟩
            · -- the body `motive t`
              try simp only [Expr.instantiate1, reduceIte, AnnotOk]
              refine ⟨(by simp [Expr.instantiate1, AnnotOk]),
                (by simp [Expr.instantiate1, AnnotOk]),
                M, t, omega, (fun _ => univ (ψ uN)),
                ?_, ?_, hMmem', htmem⟩
              · simp [interpExpr, Expr.instantiate1, updV]
              · simp [interpExpr, Expr.instantiate1, updV]
            · -- interpretability of `motive t`
              refine ⟨SetTheory.app M t, ?_⟩
              simp [interpExpr, Expr.instantiate1, updV]
          · -- interpretability of the opened body
            refine ⟨pi (ψ uN) omega (fun t => SetTheory.app M t), ?_⟩
            simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
              natA, ConstantInfo.toConstantVal, Level.eval, uN,
              -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
            try rfl
      · -- interpretability of the opened body
        refine ⟨pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          (fun _ => pi (ψ uN) omega fun t => SetTheory.app M t), ?_⟩
        simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
          hfindSc', hvalSc', natA, natSuccA,
          ConstantInfo.toConstantVal, Level.eval, uN,
          -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
        try rfl
    · -- interpretability of the opened body
      refine ⟨pi (enZ (ψ uN)) (SetTheory.app M natzero)
        (fun _ => pi (en1U (ψ uN)) (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
          (fun _ => pi (ψ uN) omega fun t => SetTheory.app M t)), ?_⟩
      simp [interpExpr, Expr.instantiate1, updV, hfindN', hvalN',
        hfindZ', hvalZ', hfindSc', hvalSc', natA, natZeroA, natSuccA,
        ConstantInfo.toConstantVal, Level.eval, uN,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl

end Setlec
