import Setlec.Model.InterpLemmas
import Setlec.Verify.InferLemmas

/-!
# The literal fragment of the model

`natLitSupported` pins the stored `Nat`/`Nat.zero`/`Nat.succ`
declarations; here the model consumes that guard: the interpretation of
a literal unfolds to the iterated `Nat.succ` value, agrees with the
constructor form the checker converts to, and — in an environment with
a model — every numeral value is a member of the `Nat` value (derived
from `EnvModel.mem_type` alone, with no `Nat`-specific model
assumptions).
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

private theorem find?_name' {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  have := List.find?_some h
  simpa using this

/-- The interpretation of a literal, unfolded through the guard. -/
theorem interpExpr_lit {cval : ConstVal V} (hs : natLitSupported env = true)
    {d : Nat} {ρ : Nat → V} {n : Nat} :
    interpExpr V cval env φ d ρ (.lit (.natVal n)) =
      some (natLitVal V (cval natZeroName φ) (cval natSuccName φ) n) := by
  simp [interpExpr, hs, Level.substFn_nil]

/-- The interpretation of `Nat` (given the guard). -/
theorem interpExpr_const_nat {cval : ConstVal V}
    (hs : natLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ (.const natName []) =
      some (cval natName φ) := by
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hsc, h1, h2, h3, -⟩ :=
    natLitSupported_inv hs
  simp [interpExpr, hn, ConstantInfo.toConstantVal, h1, Level.substFn_nil]

/-- The interpretation of `Nat.zero` (given the guard). -/
theorem interpExpr_const_natZero {cval : ConstVal V}
    (hs : natLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ (.const natZeroName []) =
      some (cval natZeroName φ) := by
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hsc, h1, h2, h3, -⟩ :=
    natLitSupported_inv hs
  simp [interpExpr, hz, ConstantInfo.toConstantVal, h2, Level.substFn_nil]

/-- The interpretation of `Nat.succ` (given the guard). -/
theorem interpExpr_const_natSucc {cval : ConstVal V}
    (hs : natLitSupported env = true) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ (.const natSuccName []) =
      some (cval natSuccName φ) := by
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hsc, h1, h2, h3, -⟩ :=
    natLitSupported_inv hs
  simp [interpExpr, hsc, ConstantInfo.toConstantVal, h3, Level.substFn_nil]

/-- The constructor form of a literal interprets to the literal's
value. -/
theorem interpExpr_natLitToConstructor {cval : ConstVal V}
    (hs : natLitSupported env = true) {d : Nat} {ρ : Nat → V} {n : Nat} :
    interpExpr V cval env φ d ρ (natLitToConstructor n) =
      some (natLitVal V (cval natZeroName φ) (cval natSuccName φ) n) := by
  cases n with
  | zero =>
    rw [natLitToConstructor]
    exact interpExpr_const_natZero hs
  | succ k =>
    obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hsc, h1, h2, h3, -⟩ :=
      natLitSupported_inv hs
    rw [natLitToConstructor]
    simp [interpExpr, hsc, ConstantInfo.toConstantVal, h3, Level.substFn_nil,
      hs, natLitVal]

/-- The interpretation of `Nat.succ` applied to one argument (given
the guard). -/
theorem interpExpr_app_succ {cval : ConstVal V}
    (hs : natLitSupported env = true) {d : Nat} {ρ : Nat → V} {x : Expr} :
    interpExpr V cval env φ d ρ (.app (.const natSuccName []) x) =
      match interpExpr V cval env φ d ρ x with
      | some vx => some (SetTheory.app (cval natSuccName φ) vx)
      | none => none := by
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hsc, h1, h2, h3, -⟩ :=
    natLitSupported_inv hs
  cases hx : interpExpr V cval env φ d ρ x with
  | none =>
    simp [interpExpr, hsc, ConstantInfo.toConstantVal, h3,
      Level.substFn_nil, hx]
  | some vx =>
    simp [interpExpr, hsc, ConstantInfo.toConstantVal, h3,
      Level.substFn_nil, hx]

/-- A whnf'd raw-literal reading interprets to the literal's value. -/
theorem interpExpr_rawNatLit {cval : ConstVal V}
    (hs : natLitSupported env = true) {a : Expr} {n : Nat}
    (ha : rawNatLit? a = some n) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ a =
      some (natLitVal V (cval natZeroName φ) (cval natSuccName φ) n) := by
  unfold rawNatLit? at ha
  split at ha
  · cases ha
    exact interpExpr_lit hs
  · next c hc =>
    split at ha <;> simp_all
    subst ha
    exact interpExpr_const_natZero hs
  · exact nomatch ha

/-- The `Nat` value lives in `univ 1` (from `mem_type` of `Nat`). -/
theorem natVal_mem_univ (m : EnvModel V env)
    (hs : natLitSupported env = true) (φ : Name → Nat) :
    m.val natName φ ∈ˢ univ 1 := by
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hsc, h1, h2, h3, h4, -⟩ :=
    natLitSupported_inv hs
  obtain ⟨tN, htN, hmemN⟩ := m.mem_type _ (find?_mem hn) φ
  rw [show (ConstantInfo.indInfo cv caps).toConstantVal = cv from rfl,
    h4] at htN
  rw [find?_name' hn] at hmemN
  simp only [interpClosed, interpExpr, Option.some.injEq] at htN
  subst htN
  simpa only [Level.eval] using hmemN

/-- The `Nat.zero` value is a member of the `Nat` value. -/
theorem natZeroVal_mem (m : EnvModel V env)
    (hs : natLitSupported env = true) (φ : Name → Nat) :
    m.val natZeroName φ ∈ˢ m.val natName φ := by
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hsc, h1, h2, h3, h4, h5,
    -⟩ := natLitSupported_inv hs
  obtain ⟨t0, ht0, hmem0⟩ := m.mem_type _ (find?_mem hz) φ
  rw [show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal = cv0 from rfl,
    h5] at ht0
  rw [find?_name' hz] at hmem0
  rw [interpClosed, interpExpr_const_nat hs] at ht0
  cases ht0
  exact hmem0

/-- The `Nat.succ` value is a member of the constant function space over
the `Nat` value. -/
theorem natSuccVal_mem_pi (m : EnvModel V env)
    (hs : natLitSupported env = true) (φ : Name → Nat) :
    m.val natSuccName φ ∈ˢ
      pi 1 (m.val natName φ) (fun _ => m.val natName φ) := by
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hsc, h1, h2, h3, h4, h5,
    nm, mb, h6, h7⟩ := natLitSupported_inv hs
  obtain ⟨t1, ht1, hmem1⟩ := m.mem_type _ (find?_mem hsc) φ
  rw [show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal = cv1 from rfl,
    h6] at ht1
  rw [find?_name' hsc] at hmem1
  rw [interpClosed, interpExpr] at ht1
  rw [h7] at ht1
  rw [interpExpr_const_nat hs] at ht1
  simp only [show ((Expr.const natName []).instantiate1
      (.fvar 0 nm (.const natName []))) = .const natName [] from rfl,
    interpExpr_const_nat hs, Option.getD_some, Option.some.injEq,
    Level.eval] at ht1
  subst ht1
  exact hmem1

/-- Every numeral value is a member of the `Nat` value — derived from
`EnvModel.mem_type` and the guard's shape facts alone. -/
theorem natLitVal_mem_nat (m : EnvModel V env)
    (hs : natLitSupported env = true) (φ : Name → Nat) (n : Nat) :
    natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) n ∈ˢ
      m.val natName φ := by
  induction n with
  | zero => exact natZeroVal_mem m hs φ
  | succ k ih =>
    exact SetTheory.app_mem (natSuccVal_mem_pi m hs φ) ih
      (fun x hx => natVal_mem_univ m hs φ)

/-- The constructor form of a literal carries truthful annotations (its
one application spine slot is semantically well-typed). -/
theorem annotOk_natLitToConstructor (m : EnvModel V env)
    (hs : natLitSupported env = true) {d : Nat} {ρ : Nat → V} {n : Nat} :
    AnnotOk V m.val env φ d ρ (natLitToConstructor n) := by
  cases n with
  | zero => rw [natLitToConstructor]; simp [AnnotOk]
  | succ k =>
    rw [natLitToConstructor]
    simp only [AnnotOk]
    refine ⟨trivial, trivial, m.val natSuccName φ,
      natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) k, 1,
      m.val natName φ, fun _ => m.val natName φ,
      interpExpr_const_natSucc hs, interpExpr_lit hs,
      natSuccVal_mem_pi m hs φ, natLitVal_mem_nat m hs φ k,
      fun x hx => natVal_mem_univ m hs φ⟩

end Setlec
