--#export S.n S.n_mk

/- Task #480: a family's former reduces through two earlier definitions, and the
   recursor's rule fires at the reduct's telescope.

   official: 0 (Lean elaborated and its kernel checked this).  con-leche: 0. -/

def A := Type
def B := A

inductive S : B
  | mk (n : Nat)

noncomputable def S.n (s : S) : Nat := S.rec (fun n => n) s

theorem S.n_mk : S.n (S.mk 1) = 1 := rfl
