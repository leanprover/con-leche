import Setlec.Kernel.TypeChecker
import Setlec.Model.FvarsOkLemmas
import Setlec.Model.Subst
import Setlec.Verify.Leaves
import Setlec.Verify.InferLemmas
import Setlec.Verify.InferLeaves
import Setlec.Model.BasisLemmas

/-!
# Shared helpers for the basis interpretation computations
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

theorem max_absorb_r' (u v : Nat) : Nat.max v (Nat.max u v) = Nat.max u v :=
  Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_max_right u v, Nat.le_refl _⟩)
    (Nat.le_max_right _ _)

theorem max_absorb_l' (u v : Nat) :
    Nat.max u (Nat.max u v) = Nat.max u v :=
  Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_refl _⟩)
    (Nat.le_max_right _ _)

theorem max_eqrec_b (u u1 : Nat) :
    Nat.max (Nat.max u (u1 + 1)) u1 = Nat.max u (u1 + 1) :=
  Nat.le_antisymm
    (Nat.max_le.mpr ⟨Nat.le_refl _,
      Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)⟩)
    (Nat.le_max_left _ _)

theorem max_eqrec_a'' (u u1 : Nat) :
    Nat.max u (Nat.max (u1 + 1) u1) = Nat.max u (u1 + 1) :=
  Nat.le_antisymm
    (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      Nat.max_le.mpr ⟨Nat.le_max_right _ _,
        Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)⟩⟩)
    (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)⟩)

theorem max_eqrec_a (u u1 : Nat) :
    Nat.max u (Nat.max (u1 + 1) (Nat.max u u1)) = Nat.max u (u1 + 1) :=
  Nat.le_antisymm
    (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      Nat.max_le.mpr ⟨Nat.le_max_right _ _,
        Nat.max_le.mpr ⟨Nat.le_max_left _ _,
          Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)⟩⟩⟩)
    (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)⟩)

theorem max_ne_zero_r {u u1 : Nat} (h : u1 ≠ 0) :
    Nat.max u u1 ≠ 0 :=
  fun hc => h (Nat.le_zero.mp (hc ▸ Nat.le_max_right u u1))

theorem max_ne_zero_l {u v : Nat} (h : u ≠ 0) : Nat.max u v ≠ 0 :=
  fun hc => h (Nat.le_zero.mp (hc ▸ Nat.le_max_left u v))

theorem max_ne_zero_r' {u v : Nat} (h : v ≠ 0) : Nat.max u v ≠ 0 :=
  fun hc => h (Nat.le_zero.mp (hc ▸ Nat.le_max_right u v))

end Setlec
