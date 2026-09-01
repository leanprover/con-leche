import Setlec.SetR.Interp2.CtxOkPKit
import Setlec.SetR.Annot.BitLemmas
import Setlec.Verify.InferLemmas

/-!
# The infer quarter, P currency — the worked ∀ clause (task #161, P3.5)

`infer_forallE_claimP` below is the P-tier mirror of
`infer_forallE_claim2D` (`Step2/InferQ.lean`), and it is the **species
example** for the whole infer quarter: every binder clause of the swap
runs the same four moves —

1. the run inversion delivers the P2 validation conjunct
   (`(zeronessOf v).equiv mb.pw`, at `μ.verified`) alongside the sort
   runs — no `sortOfE` cross-fuel gymnastics, the annotation's numeral
   is `pwBit φ mb.pw` *definitionally* (`denoteP_forallE_inv`);
2. `SortSemP` (the routed residue, `SortSem2` with `sortOfE` unfolded
   into its two checker runs and the currency upgraded) grades domain
   and opened codomain;
3. **establishment**: `AnnotValidV`'s `pi` component is
   `pwBit_zero_mem_univZero` at the conjunct + the codomain's sort
   membership — one line;
4. **the numeral bridge**: the row (`sound_pi`) speaks at the true
   sort numerals; `piR_zero_agree` carries it to the stored bit, with
   `pwBit_of_equiv_zeronessOf` supplying the zero-agreement — this is
   where residue 9's sort-agreement machinery used to live, and it is
   now a rewrite.

**Mode pinning.**  The claims (`Claims2P`) quantify `μ`, but the
*step proofs* hold at `μ.verified = true` only: the validation
conjuncts are conditional on the mode, and at `.noModel` a stored bit
is unvalidated.  The P-tier assembly (and the capstone) is a
verified-mode statement — which is the design: the annotated checker's
consistency proof covers the mode that validates.

**One routed premise is temporary**: `hCop` (the opened context) is
`CtxOkP.openS`'s conclusion, whose proof needs the `denoteP` depth
shift (batch 1); until that lands the clause takes it as a premise,
exactly where the D tier calls the kit.  TODO(#161-P3.5): replace with
`CtxOkP.openS` at the batch-1 merge.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level whnf inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- **The P-tier sort-semantics residue** (`SortSem2` transposed): a
subject whose inferred type whnfs to a sort is graded (`AnnotOkP`) and
interprets into that universe — at every checker fuel, in the fuel-free
reading.  Routed exactly as `SortSem2` is: the top-level induction is
where it becomes available. -/
def SortSemP {env : Env} (m : EnvS2UM V μ env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {e t : Expr} {u : Level} {Δa : List AVExpr}
    {ea : AVExpr},
    CtxOkP m φ d Δa e →
    inferTypeCore μ env F d e = .ok t →
    whnf μ env F d t = .ok (.sort u) →
    denoteP m.acval env φ d e = some ea →
    ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOkP V ρ ea ∧ interp2 V ρ ea ∈ˢ (univ (u.eval φ) : V)

/-- `denoteP` at a sort (the `denote2_sortQ` mirror). -/
theorem denoteP_sortQ {acval : Name → (Name → Nat) → AVExpr} {d : Nat}
    {u : Level} :
    denoteP acval env φ d (.sort u) = some (.sort (u.eval φ)) := by
  rw [denoteP]

/-- **`.forallE`, P currency** — see the module docstring; the four
moves annotated inline. -/
theorem infer_forallE_claimP (m : EnvS2UM V μ env)
    (hμ : μ.verified = true) (hss : SortSemP m μ φ)
    {d : Nat} {n : Name} {ty body t : Expr} {mb : Setlec.BinderMeta}
    {Δa : List AVExpr} {ea ta : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.forallE n ty body mb)
      = .ok t)
    (hC : CtxOkP m φ d Δa (.forallE n ty body mb))
    (hea : denoteP m.acval env φ d (.forallE n ty body mb) = some ea)
    (hta : denoteP m.acval env φ d t = some ta)
    -- TODO(#161-P3.5): `CtxOkP.openS` at the batch-1 merge
    (hCop : ∀ {tyA : AVExpr},
      denoteP m.acval env φ d ty = some tyA →
      CtxOkP m φ (d + 1) (tyA :: Δa)
        (body.instantiate1 (.fvar d n ty))) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ta) ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  -- move 1: the run inversion, validation conjunct included
  obtain ⟨tty, u, bt, v, hty, hwu, hbt, hens, hpw, rfl⟩ :=
    Setlec.inferTypeCore_forall_inv h
  have hz := hpw hμ
  obtain ⟨tyA, baA, htyA, hbaA, rfl⟩ := denoteP_forallE_inv hea
  rw [denoteP_sortQ] at hta
  obtain rfl : ta = .sort (Level.eval φ (.imax u v)) :=
    (Option.some.inj hta).symm
  -- move 2: grade domain and opened codomain through the residue
  have hdomU := hss hC.forallE_ty hty hwu htyA
  have hcodU := hss (hCop htyA) hbt
    (Setlec.ensureSortCore_inv hens) hbaA
  refine ⟨?_, ?_, ?_⟩
  · -- AnnotOkP of the ∀ node itself
    intro ρ hρ
    have hdom := hdomU ρ hρ
    have hcod : ∀ x, x ∈ˢ interp2 V ρ tyA →
        AnnotOkP V (cons x ρ) baA ∧
          interp2 V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
      fun x hx => hcodU (cons x ρ) (Sat2_cons V hρ hx)
    refine ⟨?_, ?_⟩
    · -- AnnotOk2: numerals unread
      rw [AnnotOk2_pi]
      exact ⟨hdom.1.1, fun x hx => (hcod x hx).1.1⟩
    · -- AnnotValidV: hereditary parts + the bit component
      rw [AnnotValidV_pi]
      refine ⟨hdom.1.2, fun x hx => (hcod x hx).1.2, ?_⟩
      -- move 3: establishment, one line
      intro hb x hx
      exact pwBit_zero_mem_univZero hz hb (hcod x hx).2
  · -- the sort's own grading: leaves
    intro ρ hρ
    exact ⟨by simp, by simp⟩
  · -- the membership row, through the numeral bridge
    intro ρ hρ
    have hdom := hdomU ρ hρ
    have hcod : ∀ x, x ∈ˢ interp2 V ρ tyA →
        AnnotOk2 V (cons x ρ) baA ∧
          interp2 V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
      fun x hx =>
        ⟨(hcodU (cons x ρ) (Sat2_cons V hρ hx)).1.1,
          (hcodU (cons x ρ) (Sat2_cons V hρ hx)).2⟩
    -- the row at the true sort numerals
    have hrow := sound_pi V (u := u.eval φ) (v := v.eval φ)
      hdom.1.1 (fun x hx => (hcod x hx).1) hdom.2
      (fun x hx => (hcod x hx).2)
    -- move 4: the numeral bridge (residue 9's successor is a rewrite)
    have hzag : pwBit φ mb.pw = 0 ↔ v.eval φ = 0 :=
      pwBit_of_equiv_zeronessOf hz φ
    have hbridge :
        interp2 V ρ (.pi 0 (pwBit φ mb.pw) tyA baA)
          = interp2 V ρ (.pi (u.eval φ) (v.eval φ) tyA baA) := by
      rw [interp2_pi, interp2_pi]
      exact piR_zero_agree hzag fun x _ => rfl
    rw [hbridge]
    exact hrow.2
end Setlec.SetR.Interp2
