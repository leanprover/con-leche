import Setlec.SetR.Interp2.Claims2

/-!
# `CheckStep2`, the head-normalisation quarter — Tier A clauses

Per-clause lemmas for `WhnfCoreClaims2`.  `whnfCoreBody` has nine
cases: six leaves, `.app` (β / ι / stuck), `.proj` (one reducing
against **five** stuck exits), `.letE` (ζ) and `.bvar` (throws).

Two shapes cover eight of the nine:

* **identity** — the leaves and every stuck exit return the subject, so
  the claim is `⟨rfl, id⟩`.  Stated once as `whnfStep2_id`, because
  eleven of the branches are literally that;
* **a graded step lemma** — ζ is `AnnotOk2_zeta`, β is
  `AnnotOk2_beta_pos` at a positive codomain kind and
  `AnnotOk2_beta_zero` at `0`.  Both conclude the claim's two conjuncts
  exactly, which is what those lemmas were shaped for.

The ninth is ι and it is Tier C: it enters through
`Step2Inputs.rec_rules2`, the named slot, and by the T5 rule is not
stated here.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)

universe w

variable {V : Type w} [SetTheory V]

/-- **The identity shape.**  Every leaf and every stuck exit of
`whnfCoreBody` returns its subject unchanged; the claim's two conjuncts
are then reflexivity and the identity.  Eleven branches. -/
theorem whnfStep2_id {ρ : Nat → V} (ea : AVExpr) :
    interp2 V ρ ea = interp2 V ρ ea ∧
      (AnnotOk2 V ρ ea → AnnotOk2 V ρ ea) :=
  ⟨rfl, id⟩

/-- **ζ.**  Annotation-free: `interp2`'s `letE` clause *is* the
contractum's reading, so both conjuncts come from the subject's
invariant with no premise. -/
theorem whnfStep2_zeta {ρ : Nat → V} {Ta va ba : AVExpr}
    (h : AnnotOk2 V ρ (.letE Ta va ba)) :
    interp2 V ρ (.letE Ta va ba) = interp2 V ρ (ba.inst va) ∧
      AnnotOk2 V ρ (ba.inst va) :=
  AnnotOk2_zeta V h

/-- **β at a positive codomain kind.**  No argument re-check: the slot
pins the domain through graph rigidity.  This is the fact whose runtime
twin is the per-redex beta certificate. -/
theorem whnfStep2_beta_pos {ρ : Nat → V} {v : Nat} {Aa ba aa : AVExpr}
    (hv : v ≠ 0) (h : AnnotOk2 V ρ (.app (.lam v Aa ba) aa)) :
    interp2 V ρ (.app (.lam v Aa ba) aa) = interp2 V ρ (ba.inst aa) ∧
      AnnotOk2 V ρ (ba.inst aa) :=
  AnnotOk2_beta_pos V hv h

/-- **β at kind `0`** — the `Prop`-codomain residue, which keeps its
argument membership (tasks #49/#73, unchanged by the regime split). -/
theorem whnfStep2_beta_zero {ρ : Nat → V} {Aa ba aa : AVExpr}
    (h : AnnotOk2 V ρ (.app (.lam 0 Aa ba) aa))
    (hmem : interp2 V ρ aa ∈ˢ interp2 V ρ Aa) :
    interp2 V ρ (.app (.lam 0 Aa ba) aa) = interp2 V ρ (ba.inst aa) ∧
      AnnotOk2 V ρ (ba.inst aa) :=
  AnnotOk2_beta_zero V h hmem

end Setlec.SetR.Interp2
