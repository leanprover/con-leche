import Setlec.SetR.Interp2.Claims2

/-!
# `denote2` is fuel-monotone

The one *unlisted* supplier every structural clause of the inference
quarter needs.  `Claims2`'s ledger schedules "`denote2` fuel-invariance
| `knotFuelMono`" and carries `InferFuelDet` in `Step2Inputs`; what the
clauses actually consume is the **monotone** form, and it is a theorem,
not an input: `knotFuelMono` (`SortCoh/Mono.lean`) is landed and
unconditional, `sortOfE`/`lamSortE` are the knot read through
`Except.toOption`, and `denote2`'s only fuel dependence is those two.

Why the clauses need it: `inferTypeCore` at `fuel + 1` calls its
subterms at `fuel`, so the induction hypothesis produces `denote2` at
`fuel` while the claim's conclusion is stated at `fuel + 1`.  Every
clause with a subterm crosses this gap exactly once.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf)

variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- `sortOfE` is fuel-monotone: both of its runs are. -/
theorem sortOfE_fuelMono {f f' d : Nat} {e : Expr} {u : Nat}
    (hle : f ≤ f') (h : sortOfE μ env φ f d e = some u) :
    sortOfE μ env φ f' d e = some u := by
  unfold sortOfE at h ⊢
  cases hi : inferTypeCore μ env f d e with
  | error err => rw [hi] at h; exact nomatch h
  | ok t =>
    rw [hi] at h
    simp only [Except.toOption] at h
    cases hw : whnf μ env f d t with
    | error err => rw [hw] at h; exact nomatch h
    | ok w =>
      rw [hw] at h
      rw [(knotFuelMono μ env).1 hle hi]
      simp only [Except.toOption]
      rw [(knotFuelMono μ env).2.1 hle hw]
      exact h

/-- `lamSortE` is fuel-monotone: an inference then a `sortOfE`. -/
theorem lamSortE_fuelMono {f f' d : Nat} {e : Expr} {u : Nat}
    (hle : f ≤ f') (h : lamSortE μ env φ f d e = some u) :
    lamSortE μ env φ f' d e = some u := by
  unfold lamSortE at h ⊢
  cases hi : inferTypeCore μ env f d e with
  | error err => rw [hi] at h; exact nomatch h
  | ok bt =>
    rw [hi] at h
    simp only [Except.toOption] at h
    rw [(knotFuelMono μ env).1 hle hi]
    simp only [Except.toOption]
    exact sortOfE_fuelMono hle h

/-- **`denote2` is fuel-monotone.**  Clause for clause: the leaves are
fuel-free, the structural clauses are the induction hypotheses, and the
two binder clauses are the two lemmas above. -/
theorem denote2_fuelMono {acval : Name → (Name → Nat) → AVExpr}
    {f f' : Nat} (hle : f ≤ f') :
    ∀ (d : Nat) (e : Expr) {ea : AVExpr},
      denote2 μ acval env φ f d e = some ea →
      denote2 μ acval env φ f' d e = some ea := by
  intro d e
  induction d, e using denote2.induct (env := env) with
  | case1 d u => intro ea h; rw [denote2] at h ⊢; exact h
  | case2 d idx nm ty => intro ea h; rw [denote2] at h ⊢; exact h
  | case3 d n us ci hf hlen =>
    intro ea h; rw [denote2, hf] at h ⊢; exact h
  | case4 d n us ci hf hlen =>
    intro ea h; rw [denote2, hf] at h
    dsimp only at h; rw [if_neg hlen] at h; exact nomatch h
  | case5 d n us hf =>
    intro ea h; rw [denote2, hf] at h; exact nomatch h
  | case6 d n ty body mb ihty ihbody =>
    intro ea h
    rw [denote2] at h
    rcases hta : denote2 μ acval env φ f d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denote2 μ acval env φ f (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    rcases hu : sortOfE μ env φ f d ty with _ | u
    · rw [hu] at h; exact nomatch h
    rw [hu] at h
    rcases hv : sortOfE μ env φ f (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | v
    · rw [hv] at h; exact nomatch h
    rw [hv] at h
    rw [denote2, ihty hta, ihbody hba, sortOfE_fuelMono hle hu,
      sortOfE_fuelMono hle hv]
    exact h
  | case7 d n ty body mb ihty ihbody =>
    intro ea h
    rw [denote2] at h
    rcases hta : denote2 μ acval env φ f d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denote2 μ acval env φ f (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    rcases hv : lamSortE μ env φ f (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | v
    · rw [hv] at h; exact nomatch h
    rw [hv] at h
    rw [denote2, ihty hta, ihbody hba, lamSortE_fuelMono hle hv]
    exact h
  | case8 d fe a ihf iha =>
    intro ea h
    rw [denote2] at h
    rcases hfa : denote2 μ acval env φ f d fe with _ | fa
    · rw [hfa] at h; exact nomatch h
    rw [hfa] at h
    rcases haa : denote2 μ acval env φ f d a with _ | aa
    · rw [haa] at h; exact nomatch h
    rw [haa] at h
    rw [denote2, ihf hfa, iha haa]
    exact h
  | case9 d n ty val body ihty ihval ihbody =>
    intro ea h
    rw [denote2] at h
    rcases hta : denote2 μ acval env φ f d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hva : denote2 μ acval env φ f d val with _ | va
    · rw [hva] at h; exact nomatch h
    rw [hva] at h
    rcases hba : denote2 μ acval env φ f (d + 1)
        (body.instantiate1 (.fvar d n ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    rw [denote2, ihty hta, ihval hva, ihbody hba]
    exact h
  | case10 d sn i e ihe =>
    intro ea h
    rw [denote2] at h
    rcases hea : denote2 μ acval env φ f d e with _ | ea'
    · rw [hea] at h; exact nomatch h
    rw [hea] at h
    rw [denote2, ihe hea]
    exact h
  | case11 d n hsup =>
    intro ea h
    rw [denote2, if_pos hsup] at h
    rw [denote2, if_pos hsup]
    exact h
  | case12 d n hsup =>
    intro ea h; rw [denote2, if_neg hsup] at h; exact nomatch h
  | case13 d s hsup =>
    intro ea h
    rw [denote2, if_pos hsup] at h
    rw [denote2, if_pos hsup]
    exact h
  | case14 d s hsup =>
    intro ea h; rw [denote2, if_neg hsup] at h; exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea h
    cases x with
    | bvar i => rw [denote2.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i nm ty => exact absurd rfl (hfv i nm ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE n ty b mb => exact absurd rfl (hpi n ty b mb)
    | lam n ty b mb => exact absurd rfl (hlam n ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE n ty v b => exact absurd rfl (hlet n ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

end Setlec.SetR.Interp2
