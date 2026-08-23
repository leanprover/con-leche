import Setlec.Model.Basis.PSigma.AnnotOk
import Setlec.Model.RuleFold

/-!
# `PSigma'.rec`: the total λ-equality clause of `RecRulesOk`

The canonical iota left-hand side of the single rule interprets, for
every level assignment, to the same set as the stored right-hand side:
the recursor is Prop-valued, so both bottoms collapse to the proof
point.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-! ## The canonical frame components (computed from the pinned data) -/

/-- The `α` frame variable. -/
def psigFrA : Expr :=
  .fvar 0 (Name.anonymous.str "α") (.sort (.param (Name.anonymous.str "u")))

/-- The `β` annotation. -/
def psigFrTyB : Expr :=
  .forallE (Name.anonymous.str "x") psigFrA
    (.sort (.param (Name.anonymous.str "v")))
    ⟨.default, some (.succ (.param (Name.anonymous.str "v")))⟩

/-- The `β` frame variable. -/
def psigFrB : Expr := .fvar 1 (Name.anonymous.str "β") psigFrTyB

/-- The motive annotation. -/
def psigFrTyM : Expr :=
  .forallE (Name.anonymous.str "t")
    (.app (.app (.const (Name.anonymous.str "PSigma'")
      [.param (Name.anonymous.str "u"), .param (Name.anonymous.str "v")])
      psigFrA) psigFrB)
    (.sort .zero) ⟨.default, some (.succ .zero)⟩

/-- The motive frame variable. -/
def psigFrM : Expr := .fvar 2 (Name.anonymous.str "motive") psigFrTyM

/-- The constructor head. -/
def psigFrMkC : Expr :=
  .const ((Name.anonymous.str "PSigma'").str "mk")
    [.param (Name.anonymous.str "u"), .param (Name.anonymous.str "v")]

/-- The minor-premise annotation. -/
def psigFrTyMk : Expr :=
  .forallE (Name.anonymous.str "fst") psigFrA
    (.forallE (Name.anonymous.str "snd") (.app psigFrB (.bvar 0))
      (.app psigFrM
        (.app (.app (.app (.app psigFrMkC psigFrA) psigFrB) (.bvar 1))
          (.bvar 0)))
      ⟨.default, some .zero⟩)
    ⟨.default, some (.imax (.param (Name.anonymous.str "v")) .zero)⟩

/-- The minor-premise frame variable. -/
def psigFrMk : Expr := .fvar 3 (Name.anonymous.str "mk") psigFrTyMk

/-- The first field frame variable. -/
def psigFrFst : Expr := .fvar 4 (Name.anonymous.str "fst") psigFrA

/-- The second field frame variable. -/
def psigFrSnd : Expr :=
  .fvar 5 (Name.anonymous.str "snd") (.app psigFrB psigFrFst)

/-- The recursor head of the canonical left-hand side. -/
def psigFrRec : Expr :=
  .const ((Name.anonymous.str "PSigma'").str "rec")
    [.param (Name.anonymous.str "u"), .param (Name.anonymous.str "v")]

/-! ## Prop-collapse membership helpers -/

/-- Formation of a Prop-valued `pi` inside `univ 0`. -/
theorem pi0_mem_univ0 {u' : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ univ u') (hB : ∀ x, x ∈ˢ A → B x ∈ˢ univ 0) :
    pi 0 A B ∈ˢ (univ 0 : V) := by
  have := pi_mem_univ (u := u') (v := 0) hA hB
  simpa using this

/-- The interpreted `PSigma' α β` space sits in its formation
universe. -/
theorem psigFr_sigU {A B : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) :
    SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN)) := by
  rw [psigmaVal_fold hA hB]
  exact sigma_mem_univ hA (fun x hx =>
    app_mem hB hx fun _ _ => univ_mem_univ (ψ vN))

/-- The minor-premise space is a truth value. -/
theorem psigFr_minor_mem {A B M : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN))
    (hM : M ∈ˢ pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
      fun _ => univ 0) :
    (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
      SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) ∈ˢ (univ 0 : V) := by
  have happM : ∀ x, x ∈ˢ SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B →
      SetTheory.app M x ∈ˢ univ 0 :=
    fun x hx => app_mem hM hx (fun _ _ => univ_mem_univ 0)
  have hmk4 : ∀ a, a ∈ˢ A → ∀ b, b ∈ˢ SetTheory.app B a →
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (psigmaMkVal V ψ) A) B) a) b ∈ˢ
      SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B := by
    intro a ha b hb
    rw [psigmaVal_fold hA hB]
    exact psigmaMkVal_app₄_mem hA hB ha hb
  refine pi0_mem_univ0 hA fun a ha => ?_
  have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
    app_mem hB ha fun _ _ => univ_mem_univ (ψ vN)
  exact pi0_mem_univ0 hBa fun b hb => happM _ (hmk4 a ha b hb)

/-- The residual motive space (over the major premise) is a truth
value. -/
theorem psigFr_S4 {A B M : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN))
    (hM : M ∈ˢ pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
      fun _ => univ 0) :
    (pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
      fun t => SetTheory.app M t) ∈ˢ (univ 0 : V) :=
  pi0_mem_univ0 (psigFr_sigU hA hB)
    (fun _ ht => app_mem hM ht (fun _ _ => univ_mem_univ 0))

theorem psigFr_S3 {A B M : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN))
    (hM : M ∈ˢ pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
      fun _ => univ 0) :
    (pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
      fun _ => pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun t => SetTheory.app M t) ∈ˢ (univ 0 : V) :=
  pi0_mem_univ0 (psigFr_minor_mem hA hB hM)
    (fun _ _ => psigFr_S4 hA hB hM)

theorem psigFr_S2 {A B : V} (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) :
    (pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0)
      fun M => pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
        fun _ => pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
          fun t => SetTheory.app M t) ∈ˢ (univ 0 : V) := by
  have hdom : (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
      fun _ => univ 0) ∈ˢ
      univ (Nat.max (Nat.max (ψ uN) (ψ vN)) 1) := by
    have := pi_mem_univ (u := Nat.max (ψ uN) (ψ vN)) (v := 1)
      (psigFr_sigU hA hB) (fun _ _ => univ_mem_univ 0)
    simpa using this
  exact pi0_mem_univ0 hdom (fun M hM => psigFr_S3 hA hB hM)

theorem psigFr_S1 {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    (pi 0 (pi (ψ vN + 1) A fun _ => univ (ψ vN))
      fun B => pi 0 (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
          fun _ => univ 0)
        fun M => pi 0 (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
            SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (psigmaMkVal V ψ) A) B) a) b))
          fun _ => pi 0 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            fun t => SetTheory.app M t) ∈ˢ (univ 0 : V) := by
  have hdom : (pi (ψ vN + 1) A fun _ => univ (ψ vN)) ∈ˢ
      univ (Nat.max (ψ uN) (ψ vN + 1)) :=
    pi_mem_univ (u := ψ uN) (v := ψ vN + 1) hA
      (fun _ _ => univ_mem_univ (ψ vN))
  exact pi0_mem_univ0 hdom (fun B hB => psigFr_S2 hA hB)

/-! ## Stage facts -/

theorem psigFr_interp_tyB {cval : ConstVal V} {A : V} :
    interpExpr V cval env ψ 1 (updV V (rho0 V) 0 A) psigFrTyB =
      some (pi (ψ vN + 1) A fun _ => univ (ψ vN)) := by
  simp [psigFrTyB, psigFrA, interpExpr, Expr.instantiate1, updV, Level.eval,
    vN]
  try rfl

theorem psigFr_annotOk_tyB {cval : ConstVal V} {A : V} :
    AnnotOk V cval env ψ 1 (updV V (rho0 V) 0 A) psigFrTyB := by
  simp only [psigFrTyB, psigFrA, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro x Sx hSx hx
  refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
  intro v hv
  obtain rfl := Option.some.inj hv
  refine ⟨univ (ψ vN), ?_, ?_⟩
  · simp [interpExpr, Expr.instantiate1, updV, Level.eval, vN]
  · exact univ_mem_univ (ψ vN)

theorem psigFr_interp_tyM {cval : ConstVal V} {A B : V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ') :
    interpExpr V cval env ψ 2 (updV V (updV V (rho0 V) 0 A) 1 B) psigFrTyM =
      some (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
        fun _ => univ 0) := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA :=
    hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  simp [psigFrTyM, psigFrA, psigFrB, psigFrTyB, interpExpr,
    Expr.instantiate1, updV, hfindS', hvalS', psigmaA,
    ConstantInfo.toConstantVal, Level.eval]
  try rfl

theorem psigFr_annotOk_tyM {cval : ConstVal V} {A B : V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN)) :
    AnnotOk V cval env ψ 2 (updV V (updV V (rho0 V) 0 A) 1 B) psigFrTyM := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA :=
    hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  simp only [psigFrTyM, psigFrA, psigFrB, psigFrTyB, AnnotOk]
  refine ⟨⟨⟨trivial, trivial,
      psigmaVal V ψ, A,
      Nat.max (Nat.max (ψ uN) (ψ vN + 1)) (Nat.max (ψ uN) (ψ vN) + 1),
      univ (ψ uN),
      (fun X => pi (Nat.max (ψ uN) (ψ vN) + 1)
        (pi (ψ vN + 1) X fun _ => univ (ψ vN)) fun _ =>
          univ (Nat.max (ψ uN) (ψ vN))),
      ?_, ?_, psigmaVal_mem, hA, ?_⟩,
    trivial,
    SetTheory.app (psigmaVal V ψ) A, B,
    Nat.max (ψ uN) (ψ vN) + 1,
    pi (ψ vN + 1) A (fun _ => univ (ψ vN)),
    (fun _ => univ (Nat.max (ψ uN) (ψ vN))),
    ?_, ?_, psigmaVal_app_mem hA, hB,
    fun _ _ => univ_mem_univ (Nat.max (ψ uN) (ψ vN))⟩,
    ⟨_, rfl⟩, ?_⟩
  · simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS', psigmaA,
      ConstantInfo.toConstantVal]
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
  · rw [interpExpr]
    simp [interpExpr, Expr.instantiate1, updV, hfindS', hvalS', psigmaA,
      ConstantInfo.toConstantVal]
    try rfl
  · simp [interpExpr, Expr.instantiate1, updV]
  · intro t St hSt ht
    refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨univ 0, ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, Level.eval]
    · exact univ_mem_univ 0

theorem psigFr_interp_tyMk {cval : ConstVal V} {A B M : V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ') :
    interpExpr V cval env ψ 3
      (updV V (updV V (updV V (rho0 V) 0 A) 1 B) 2 M) psigFrTyMk =
      some (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
        SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA :=
    hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  have hfindM' : env.find? ((Name.anonymous.str "PSigma'").str "mk") =
      some psigmaMkA := hfindM
  have hvalM' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PSigma'").str "mk") ψ' = psigmaMkVal V ψ' :=
    hvalM
  simp [psigFrTyMk, psigFrMkC, psigFrA, psigFrB, psigFrTyB, psigFrM,
    psigFrTyM, interpExpr, Expr.instantiate1, updV, hfindS', hvalS',
    hfindM', hvalM', psigmaA, psigmaMkA, ConstantInfo.toConstantVal,
    Level.eval,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

theorem psigFr_annotOk_tyMk {cval : ConstVal V} {A B M : V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ')
    (hA : A ∈ˢ univ (ψ uN))
    (hB : B ∈ˢ pi (ψ vN + 1) A fun _ => univ (ψ vN))
    (hM : M ∈ˢ pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
      fun _ => univ 0) :
    AnnotOk V cval env ψ 3
      (updV V (updV V (updV V (rho0 V) 0 A) 1 B) 2 M) psigFrTyMk := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA :=
    hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  have hfindM' : env.find? ((Name.anonymous.str "PSigma'").str "mk") =
      some psigmaMkA := hfindM
  have hvalM' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PSigma'").str "mk") ψ' = psigmaMkVal V ψ' :=
    hvalM
  have happM : ∀ x, x ∈ˢ SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B →
      SetTheory.app M x ∈ˢ univ 0 :=
    fun x hx => app_mem hM hx (fun _ _ => univ_mem_univ 0)
  have hmk4 : ∀ a, a ∈ˢ A → ∀ b, b ∈ˢ SetTheory.app B a →
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (psigmaMkVal V ψ) A) B) a) b ∈ˢ
      SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B := by
    intro a ha b hb
    rw [psigmaVal_fold hA hB]
    exact psigmaMkVal_app₄_mem hA hB ha hb
  simp only [psigFrTyMk, psigFrMkC, psigFrA, psigFrB, psigFrTyB, psigFrM,
    psigFrTyM, AnnotOk]
  refine ⟨trivial, ⟨_, rfl⟩, ?_⟩
  intro a Sa hSa ha
  have hSa' : Sa = A := by
    simp [interpExpr, Expr.instantiate1, updV] at hSa
    exact hSa.symm
  rw [hSa'] at ha
  refine ⟨?_, ?_⟩
  · -- opened `∀ (snd : β fst), motive (mk α β fst snd)`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨⟨(by simp [Expr.instantiate1, AnnotOk]),
      (by simp [Expr.instantiate1, AnnotOk]), B, a, ψ vN + 1, A,
      (fun _ => univ (ψ vN)), ?_, ?_, hB, ha,
      fun _ _ => univ_mem_univ (ψ vN)⟩, ⟨_, rfl⟩, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV]
    · simp [interpExpr, Expr.instantiate1, updV]
    intro b Sb hSb hb
    have hSb' : Sb = SetTheory.app B a := by
      simp [interpExpr, Expr.instantiate1, updV,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff] at hSb
      exact hSb.symm
    rw [hSb'] at hb
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
          ?_, ?_, psigmaMkVal_mem, hA,
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
          ?_, ?_, psigmaMkVal_app_mem hA, hB,
          fun B' hB' => psigmaMk_space2 hA hB'⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
          SetTheory.app (SetTheory.app (psigmaMkVal V ψ) A) B,
          a, Nat.max (ψ uN) (ψ vN), A,
          (fun a' => pi (Nat.max (ψ uN) (ψ vN))
            (SetTheory.app B a') fun _ =>
            sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
              SetTheory.app B x),
          ?_, ?_, psigmaMkVal_app₂_mem hA hB, ha,
          fun a' ha' => psigmaMk_space3 hA hB ha'⟩,
        (by simp [Expr.instantiate1, AnnotOk]),
          SetTheory.app (SetTheory.app (SetTheory.app
            (psigmaMkVal V ψ) A) B) a,
          b, Nat.max (ψ uN) (ψ vN), SetTheory.app B a,
          (fun _ => sigmaSet (Nat.max (ψ uN) (ψ vN)) A fun x =>
            SetTheory.app B x),
          ?_, ?_, psigmaMkVal_app₃_mem hA hB ha, hb,
          fun _ _ => sigma_mem_univ hA (fun x hx =>
            app_mem hB hx fun _ _ => univ_mem_univ (ψ vN))⟩,
        M,
        SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (psigmaMkVal V ψ) A) B) a) b,
        1,
        SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B,
        (fun _ => univ 0),
        ?_, ?_, hM, hmk4 a ha b hb,
        fun _ _ => univ_mem_univ 0⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindM', hvalM',
          psigmaMkA, ConstantInfo.toConstantVal]
        try rfl
      · simp [interpExpr, Expr.instantiate1, updV]
      · rw [interpExpr]
        simp [interpExpr, Expr.instantiate1, updV, hfindM', hvalM',
          psigmaMkA, ConstantInfo.toConstantVal]
        try rfl
      · simp [interpExpr, Expr.instantiate1, updV]
      · rw [interpExpr]
        simp [interpExpr, Expr.instantiate1, updV, hfindM', hvalM',
          psigmaMkA, ConstantInfo.toConstantVal]
        try rfl
      · simp [interpExpr, Expr.instantiate1, updV]
      · rw [interpExpr]
        simp [interpExpr, Expr.instantiate1, updV, hfindM', hvalM',
          psigmaMkA, ConstantInfo.toConstantVal]
        try rfl
      · simp [interpExpr, Expr.instantiate1, updV]
      · simp [interpExpr, Expr.instantiate1, updV]
      · rw [interpExpr]
        simp [interpExpr, Expr.instantiate1, updV, hfindM', hvalM',
          psigmaMkA, ConstantInfo.toConstantVal]
        try rfl
    · -- fibre-universe of `snd` (annotation `0`)
      intro v hv
      obtain rfl := Option.some.inj hv
      refine ⟨SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (psigmaMkVal V ψ) A) B) a) b), ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, hfindM', hvalM',
          psigmaMkA, ConstantInfo.toConstantVal]
        try rfl
      · exact happM _ (hmk4 a ha b hb)
  · -- fibre-universe of `fst` (annotation `imax v 0`)
    intro v hv
    obtain rfl := Option.some.inj hv
    refine ⟨pi 0 (SetTheory.app B a) (fun b =>
      SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindM', hvalM',
        psigmaMkA, ConstantInfo.toConstantVal, Level.eval,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · have hBa : SetTheory.app B a ∈ˢ univ (ψ vN) :=
        app_mem hB ha fun _ _ => univ_mem_univ (ψ vN)
      exact pi_mem_univ (u := ψ vN) (v := 0) hBa
        (fun b hb => happM _ (hmk4 a ha b hb))

/-! ## The `RecRulesOk` clause of the rule -/

/-- The `RecRulesOk` clause of `PSigma'.rec`'s single rule. -/
theorem psigmaRec_ruleOk {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ')
    (hfindR : env.find? (psigmaName.str "rec") = some psigmaRecA)
    (hvalR : ∀ ψ' : Name → Nat,
      cval (psigmaName.str "rec") ψ' = psigmaRecVal V ψ') :
    ∃ fvms bL,
      ruleLhsParts (psigmaName.str "rec") psigmaRecA.toConstantVal 4
        ((ConstantInfo.recRules psigmaRecA).getD 0 default)
        psigmaMkA.toConstantVal = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = 4 +
        RecRule.nfields ((ConstantInfo.recRules psigmaRecA).getD 0 default) ∧
      (closeLamsAt fvms bL).constsResolve env = true ∧
      ∀ ψ' : Name → Nat,
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' psigmaRecRhsA = some Rv := by
  have hfindS' : env.find? (Name.anonymous.str "PSigma'") = some psigmaA :=
    hfindS
  have hvalS' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "PSigma'") ψ' = psigmaVal V ψ' := hvalS
  have hfindM' : env.find? ((Name.anonymous.str "PSigma'").str "mk") =
      some psigmaMkA := hfindM
  have hvalM' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PSigma'").str "mk") ψ' = psigmaMkVal V ψ' :=
    hvalM
  have hfindR' : env.find? ((Name.anonymous.str "PSigma'").str "rec") =
      some psigmaRecA := hfindR
  have hvalR' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "PSigma'").str "rec") ψ' =
        psigmaRecVal V ψ' := hvalR
  have hparts : ruleLhsParts (psigmaName.str "rec") psigmaRecA.toConstantVal 4
      ((ConstantInfo.recRules psigmaRecA).getD 0 default)
      psigmaMkA.toConstantVal = some
      ([(psigFrA, ⟨.implicit, some (.imax
          (.imax (.param (Name.anonymous.str "u"))
            (.succ (.param (Name.anonymous.str "v"))))
          (.imax (.imax (.max (.param (Name.anonymous.str "u"))
              (.param (Name.anonymous.str "v"))) (.succ .zero))
            (.imax (.imax (.param (Name.anonymous.str "u"))
                (.imax (.param (Name.anonymous.str "v")) .zero))
              (.imax (.param (Name.anonymous.str "u"))
                (.imax (.param (Name.anonymous.str "v")) .zero)))))⟩),
        (psigFrB, ⟨.default, some (.imax
          (.imax (.max (.param (Name.anonymous.str "u"))
            (.param (Name.anonymous.str "v"))) (.succ .zero))
          (.imax (.imax (.param (Name.anonymous.str "u"))
              (.imax (.param (Name.anonymous.str "v")) .zero))
            (.imax (.param (Name.anonymous.str "u"))
              (.imax (.param (Name.anonymous.str "v")) .zero))))⟩),
        (psigFrM, ⟨.default, some (.imax
          (.imax (.param (Name.anonymous.str "u"))
            (.imax (.param (Name.anonymous.str "v")) .zero))
          (.imax (.param (Name.anonymous.str "u"))
            (.imax (.param (Name.anonymous.str "v")) .zero)))⟩),
        (psigFrMk, ⟨.default, some (.imax (.param (Name.anonymous.str "u"))
          (.imax (.param (Name.anonymous.str "v")) .zero))⟩),
        (psigFrFst, ⟨.default,
          some (.imax (.param (Name.anonymous.str "v")) .zero)⟩),
        (psigFrSnd, ⟨.default, some .zero⟩)],
       .app (.app (.app (.app (.app psigFrRec psigFrA) psigFrB) psigFrM)
           psigFrMk)
         (.app (.app (.app (.app psigFrMkC psigFrA) psigFrB) psigFrFst)
           psigFrSnd)) := by rfl
  obtain ⟨hwf, hlen⟩ := ruleLhsParts_frameWf hparts rfl rfl rfl rfl
    (fun _ _ h => nomatch h)
  refine ⟨_, _, hparts, hwf, hlen, ?_, ?_⟩
  · exact ruleLhsParts_resolve hparts
      (by rw [hfindR]; rfl)
      (show (env.find? ((Name.anonymous.str "PSigma'").str "mk")).isSome =
          true by rw [hfindM']; rfl)
      (by simp [ConstantInfo.toConstantVal, psigmaRecA, Expr.constsResolve,
        hfindS', hfindM'])
      (by simp [ConstantInfo.toConstantVal, psigmaMkA, Expr.constsResolve,
        hfindS'])
      (fun _ _ h => nomatch h)
  · intro ψ'
    have hAR : AnnotOk V cval env ψ' 0 (rho0 V) psigmaRecRhsA :=
      annotOk_psigmaRec_rhs (cval := cval) (ψ := ψ') hfindS hvalS hfindM
        hvalM
    have hstep : ∀ {fvms : List (Expr × BinderMeta)} {bL : Expr},
        FrameWf 0 fvms bL →
        TowerOk (V := V) cval env ψ' 0 (rho0 V) fvms bL psigmaRecRhsA →
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' psigmaRecRhsA = some Rv := by
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
    refine TowerOk.cons (A := pi (ψ' vN + 1) A fun _ => univ (ψ' vN))
      (psigFr_interp_tyB (cval := cval)) (psigFr_interp_tyB (cval := cval))
      (psigFr_annotOk_tyB (cval := cval)) ?_
    intro B hB
    refine TowerOk.cons (A := pi 1
        (SetTheory.app (SetTheory.app (psigmaVal V ψ') A) B) fun _ => univ 0)
      (psigFr_interp_tyM hfindS hvalS) (psigFr_interp_tyM hfindS hvalS)
      (psigFr_annotOk_tyM hfindS hvalS hA hB) ?_
    intro M hM
    refine TowerOk.cons (A := pi 0 A fun a =>
        pi 0 (SetTheory.app B a) fun b =>
          SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (psigmaMkVal V ψ') A) B) a) b))
      (psigFr_interp_tyMk hfindS hvalS hfindM hvalM)
      (psigFr_interp_tyMk hfindS hvalS hfindM hvalM)
      (psigFr_annotOk_tyMk hfindS hvalS hfindM hvalM hA hB hM) ?_
    intro mk hmk
    have hityFst : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B) 2 M) 3 mk)
        psigFrA = some A := by
      simp [psigFrA, interpExpr, updV]
    refine TowerOk.cons (A := A) hityFst hityFst
      (by simp [psigFrA, AnnotOk]) ?_
    intro a ha
    have hitySnd : interpExpr V cval env ψ' 5
        (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B) 2 M) 3 mk)
          4 a)
        (.app psigFrB psigFrFst) = some (SetTheory.app B a) := by
      simp [psigFrB, psigFrTyB, psigFrFst, psigFrA, interpExpr, updV]
    refine TowerOk.cons (A := SetTheory.app B a) hitySnd hitySnd
      (by simp only [psigFrB, psigFrTyB, psigFrFst, psigFrA, AnnotOk]
          exact ⟨trivial, trivial, B, a, ψ' vN + 1, A,
            (fun _ => univ (ψ' vN)),
            (by simp [interpExpr, updV]), (by simp [interpExpr, updV]),
            hB, ha, fun _ _ => univ_mem_univ _⟩) ?_
    intro b hb
    -- the bottom frame valuation
    have hmkpt : mk = pt :=
      mem_univ_zero (psigFr_minor_mem hA hB hM) hmk
    have hsub2 : Level.substFn ψ'
        [Name.anonymous.str "u", Name.anonymous.str "v"]
        [Level.param (Name.anonymous.str "u"),
         Level.param (Name.anonymous.str "v")] = ψ' :=
      funext fun _ => Level.substFn_map_param
    have hirec : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) psigFrRec = some (psigmaRecVal V ψ') := by
      simp only [psigFrRec, interpExpr, hfindR', psigmaRecA,
        ConstantInfo.toConstantVal, List.length_cons, List.length_nil,
        reduceIte, hsub2, hvalR']
    have himkC : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) psigFrMkC = some (psigmaMkVal V ψ') := by
      simp only [psigFrMkC, interpExpr, hfindM', psigmaMkA,
        ConstantInfo.toConstantVal, List.length_cons, List.length_nil,
        reduceIte, hsub2, hvalM']
    have hifvA : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) psigFrA = some A := by
      simp [psigFrA, interpExpr, updV]
    have hifvB : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) psigFrB = some B := by
      simp [psigFrB, interpExpr, updV]
    have hifvM : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) psigFrM = some M := by
      simp [psigFrM, interpExpr, updV]
    have hifvMk : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) psigFrMk = some mk := by
      simp [psigFrMk, interpExpr, updV]
    have hifvFst : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) psigFrFst = some a := by
      simp [psigFrFst, interpExpr, updV]
    have hifvSnd : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) psigFrSnd = some b := by
      simp [psigFrSnd, interpExpr, updV]
    have hip1 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) (.app psigFrRec psigFrA) =
        some (SetTheory.app (psigmaRecVal V ψ') A) := by
      rw [interpExpr, hirec, hifvA]
    have hip2 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) (.app (.app psigFrRec psigFrA) psigFrB) =
        some (SetTheory.app (SetTheory.app (psigmaRecVal V ψ') A) B) := by
      rw [interpExpr, hip1, hifvB]
    have hip3 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b)
        (.app (.app (.app psigFrRec psigFrA) psigFrB) psigFrM) =
        some (SetTheory.app (SetTheory.app (SetTheory.app
          (psigmaRecVal V ψ') A) B) M) := by
      rw [interpExpr, hip2, hifvM]
    have hip4 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b)
        (.app (.app (.app (.app psigFrRec psigFrA) psigFrB) psigFrM)
          psigFrMk) =
        some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (psigmaRecVal V ψ') A) B) M) mk) := by
      rw [interpExpr, hip3, hifvMk]
    have hiq1 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) (.app psigFrMkC psigFrA) =
        some (SetTheory.app (psigmaMkVal V ψ') A) := by
      rw [interpExpr, himkC, hifvA]
    have hiq2 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b) (.app (.app psigFrMkC psigFrA) psigFrB) =
        some (SetTheory.app (SetTheory.app (psigmaMkVal V ψ') A) B) := by
      rw [interpExpr, hiq1, hifvB]
    have hiq3 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b)
        (.app (.app (.app psigFrMkC psigFrA) psigFrB) psigFrFst) =
        some (SetTheory.app (SetTheory.app (SetTheory.app
          (psigmaMkVal V ψ') A) B) a) := by
      rw [interpExpr, hiq2, hifvFst]
    have hiq4 : interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b)
        (.app (.app (.app (.app psigFrMkC psigFrA) psigFrB) psigFrFst)
          psigFrSnd) =
        some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (psigmaMkVal V ψ') A) B) a) b) := by
      rw [interpExpr, hiq3, hifvSnd]
    -- the recursor value's membership in its interpreted type
    obtain ⟨T, hT, hmem⟩ := psigmaRec_key (cval := cval) (env := env)
      (ψ := ψ') hfindS hvalS hfindM hvalM
    rw [interp_psigmaRec_type hfindS hvalS hfindM hvalM] at hT
    obtain rfl := Option.some.inj hT
    have hm1 := app_mem hmem hA (fun A' hA' => psigFr_S1 hA')
    have hm2 := app_mem hm1 hB (fun B' hB' => psigFr_S2 hA hB')
    have hm3 := app_mem hm2 hM (fun M' hM' => psigFr_S3 hA hB hM')
    have hm4 := app_mem hm3 hmk (fun _ _ => psigFr_S4 hA hB hM)
    have hqv : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (psigmaMkVal V ψ') A) B) a) b ∈ˢ
        SetTheory.app (SetTheory.app (psigmaVal V ψ') A) B := by
      rw [psigmaVal_fold hA hB]
      exact psigmaMkVal_app₄_mem hA hB ha hb
    refine TowerOk.nil (w := pt) ?_ ?_ ?_
    · rw [interpExpr, hip4, hiq4]
      show some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (psigmaRecVal V ψ') A) B) M) mk)
        (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (psigmaMkVal V ψ') A) B) a) b)) = some pt
      rw [show (psigmaRecVal V ψ' : V) = pt from by
        simp only [psigmaRecVal]; exact lam_zero]
      simp only [app_pt]
    · show interpExpr V cval env ψ' 6
        (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
          2 M) 3 mk) 4 a) 5 b)
        (.app (.app psigFrMk psigFrFst) psigFrSnd) = some pt
      have hmka : interpExpr V cval env ψ' 6
          (updV V (updV V (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 B)
            2 M) 3 mk) 4 a) 5 b) (.app psigFrMk psigFrFst) =
          some (SetTheory.app mk a) := by
        rw [interpExpr, hifvMk, hifvFst]
      rw [interpExpr, hmka, hifvSnd]
      show some (SetTheory.app (SetTheory.app mk a) b) = some pt
      rw [hmkpt]
      rw [app_pt, app_pt]
    · simp only [AnnotOk, psigFrRec, psigFrMkC, psigFrA, psigFrB, psigFrTyB,
        psigFrM, psigFrTyM, psigFrMk, psigFrTyMk, psigFrFst, psigFrSnd]
      exact ⟨⟨⟨⟨⟨trivial, trivial,
          psigmaRecVal V ψ', A, 0, univ (ψ' uN), _,
          hirec, hifvA, hmem, hA, fun A' hA' => psigFr_S1 hA'⟩,
        trivial,
        SetTheory.app (psigmaRecVal V ψ') A, B, 0,
          pi (ψ' vN + 1) A (fun _ => univ (ψ' vN)), _,
          hip1, hifvB, hm1, hB, fun B' hB' => psigFr_S2 hA hB'⟩,
        trivial,
        SetTheory.app (SetTheory.app (psigmaRecVal V ψ') A) B, M, 0,
          pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ') A) B)
            (fun _ => univ 0), _,
          hip2, hifvM, hm2, hM, fun M' hM' => psigFr_S3 hA hB hM'⟩,
        trivial,
        SetTheory.app (SetTheory.app (SetTheory.app (psigmaRecVal V ψ') A)
          B) M, mk, 0,
          pi 0 A (fun a' => pi 0 (SetTheory.app B a') fun b' =>
            SetTheory.app M (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (psigmaMkVal V ψ') A) B) a') b')), _,
          hip3, hifvMk, hm3, hmk, fun _ _ => psigFr_S4 hA hB hM⟩,
        ⟨⟨⟨⟨trivial, trivial,
            psigmaMkVal V ψ', A,
            (if Nat.max (ψ' uN) (ψ' vN) = 0 then 0
              else Nat.max (ψ' uN) (ψ' vN + 1)),
            univ (ψ' uN), _,
            himkC, hifvA, psigmaMkVal_mem, hA,
            fun X hX => psigmaMk_space1 hX⟩,
          trivial,
          SetTheory.app (psigmaMkVal V ψ') A, B, Nat.max (ψ' uN) (ψ' vN),
            pi (ψ' vN + 1) A (fun _ => univ (ψ' vN)), _,
            hiq1, hifvB, psigmaMkVal_app_mem hA, hB,
            fun B' hB' => psigmaMk_space2 hA hB'⟩,
          trivial,
          SetTheory.app (SetTheory.app (psigmaMkVal V ψ') A) B, a,
            Nat.max (ψ' uN) (ψ' vN), A, _,
            hiq2, hifvFst, psigmaMkVal_app₂_mem hA hB, ha,
            fun a' ha' => psigmaMk_space3 hA hB ha'⟩,
          trivial,
          SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkVal V ψ') A)
            B) a, b, Nat.max (ψ' uN) (ψ' vN), SetTheory.app B a, _,
            hiq3, hifvSnd, psigmaMkVal_app₃_mem hA hB ha, hb,
            fun _ _ => sigma_mem_univ hA (fun x hx =>
              app_mem hB hx fun _ _ => univ_mem_univ (ψ' vN))⟩,
        SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (psigmaRecVal V ψ') A) B) M) mk,
        SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (psigmaMkVal V ψ') A) B) a) b,
        0, SetTheory.app (SetTheory.app (psigmaVal V ψ') A) B,
        (fun t => SetTheory.app M t),
        hip4, hiq4, hm4, hqv,
        fun t ht => app_mem hM ht (fun _ _ => univ_mem_univ 0)⟩

end Setlec
