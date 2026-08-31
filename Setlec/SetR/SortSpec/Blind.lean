import Setlec.SetR.SortSpec.Defs

/-!
# Argument-blindness, checked

Seal 0's (P3) says argument-blindness is the pilot's structural
advantage over the `(F)` species, and that it "must be checked, not
assumed, at the ι clause, where the motive *is* an argument".

Here it is checked, and it holds in the strongest possible form: an
application spine's structural sort depends on the head and on the
**number** of arguments, and on nothing else.  `sortApp_mkAppN` says
exactly that, and the ι clause is an instance of it — a recursor
application's motive is one of the discarded arguments.

The price is paid elsewhere, and it is paid honestly: because the
motive is never read, the *value* of a recursor application's sort is
`none` whenever the declared codomain is a motive application rather
than a syntactic sort.  See `SortSpec/DESIGN.md` seal 1 and the ι
probe in `SortSpec/Examples.lean`.
-/

namespace Setlec.SetR.SortSpec

open Setlec (Expr Level Name)

/-- One argument is discarded, definitionally. -/
theorem sortApp_arg_blind (σ : SortEnv) (g : List Expr)
    (f a a' : Expr) (n : Nat) :
    sortApp σ g (.app f a) n = sortApp σ g (.app f a') n := rfl

/-- **The whole spine is discarded; only its length survives.** -/
theorem sortApp_mkAppN (σ : SortEnv) (g : List Expr) :
    ∀ (as : List Expr) (f : Expr) (n : Nat),
      sortApp σ g (Expr.mkAppN f as) n
        = sortApp σ g f (n + as.length) := by
  intro as
  induction as with
  | nil => intro f n; rfl
  | cons a as ih =>
    intro f n
    rw [Expr.mkAppN, ih (.app f a) n, sortApp_app]
    simp [Nat.add_assoc]

/-- Consequently: two spines on the same head with the same number of
arguments have the same structural sort, whatever the arguments are.
For a recursor head this is the ι clause: the motive is one of `as`. -/
theorem sortApp_spine_blind (σ : SortEnv) (g : List Expr) (f : Expr)
    (as as' : List Expr) (n : Nat) (hlen : as.length = as'.length) :
    sortApp σ g (Expr.mkAppN f as) n
      = sortApp σ g (Expr.mkAppN f as') n := by
  rw [sortApp_mkAppN, sortApp_mkAppN, hlen]

/-- A `let`'s value is discarded too (the kernel substitutes it; the
structural sort reads the *annotation* instead). -/
theorem sortApp_letVal_blind (σ : SortEnv) (g : List Expr)
    (nm : Name) (t v v' b : Expr) (n : Nat) :
    sortApp σ g (.letE nm t v b) n
      = sortApp σ g (.letE nm t v' b) n := rfl

end Setlec.SetR.SortSpec
