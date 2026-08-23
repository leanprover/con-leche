import Setlec.Model.Basis.PSigma.Iota
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
    (fun t ht => app_mem hM ht (fun _ _ => univ_mem_univ 0))

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

end Setlec
