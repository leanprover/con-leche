module

public import ConLeche.Verify.ProjSlots
public import ConLeche.Kernel.TypeChecker
import ConLeche.Verify.InferLemmas

public section

/-!
# A successful inference names only occupied projection slots

`inferTypeCore_projSlotsOk`: the full-grade inference visits every
subterm of its subject (the ∀/λ domains and opened bodies, both halves
of an application, a projection's subject), and its `.proj` clause
succeeds only at an occupied table slot of the node's own structure
name (`inferTypeCore_proj_inv`: `findProj? T i = some _` with `T = sn`).
So an inferred subject whose fvar annotations are slot-correct
(`FvarTysOk`, vacuous at a closed subject) has an occupied slot at
every `.proj` node (`ProjSlotsOk`), hence no `.proj` node at an EMPTY
slot (`inferTypeCore_noProjAt`).

This is the source of the stored-term fact `NoProjAt` for a term
stored WITHOUT an annotation pass but checked by a full inference —
the generated recursor types and rules (`classConstOk`, the rule
records' `htyR`).  It needs no environment invariant: inference never
reads a slot's contents into its subject, only its presence.
-/

namespace ConLeche

open ConLeche.Expr

namespace Expr

variable {env : Env}

/-- Instantiation only replaces bound variables: a slot-correct
instance comes from a slot-correct subject. -/
theorem ProjSlotsOk.of_instantiate1 {v : Expr} :
    ∀ (e : Expr) (d : Nat), ProjSlotsOk env (e.instantiate1 v d) → ProjSlotsOk env e := by
  intro e
  induction e with
  | bvar j => intro _ _; simp
  | sort u => intro _ _; simp
  | const n us => intro _ _; simp
  | lit l => intro _ _; simp
  | fvar idx ty => intro d h; rw [Expr.instantiate1] at h; exact h
  | app f a ihf iha =>
    intro d h
    rw [Expr.instantiate1, projSlotsOk_app] at h
    exact projSlotsOk_app.mpr ⟨ihf d h.1, iha d h.2⟩
  | lam ty b m ihty ihb =>
    intro d h
    rw [Expr.instantiate1, projSlotsOk_lam] at h
    exact projSlotsOk_lam.mpr ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro d h
    rw [Expr.instantiate1, projSlotsOk_forallE] at h
    exact projSlotsOk_forallE.mpr ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d h
    rw [Expr.instantiate1, projSlotsOk_letE] at h
    exact projSlotsOk_letE.mpr ⟨iht d h.1, ihval d h.2.1, ihb (d + 1) h.2.2⟩
  | proj s j e ihe =>
    intro d h
    rw [Expr.instantiate1, projSlotsOk_proj] at h
    exact projSlotsOk_proj.mpr ⟨h.1, ihe d h.2⟩

end Expr

variable {mode : CheckMode}

/-- **A successful full-grade inference names only occupied slots**:
every `.proj` node of the subject has a table entry at its own
structure name, given slot-correct fvar annotations. -/
theorem inferTypeCore_projSlotsOk {env : Env} :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCore mode env fuel d e = .ok t → FvarTysOk env e → ProjSlotsOk env e
  | 0, _, _, _, h, _ => by rw [inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, d, e, t, h, hf => by
    cases e with
    | bvar j => simp
    | sort u => simp
    | const n us => simp
    | lit l => simp
    | fvar idx ty => exact projSlotsOk_fvar.mpr (fvarTysOk_fvar.mp hf)
    | app f a =>
      obtain ⟨tf, -, -, -, h1, -, -, ta, h2, -⟩ := inferTypeCore_app_inv h
      rw [fvarTysOk_app] at hf
      exact projSlotsOk_app.mpr
        ⟨inferTypeCore_projSlotsOk fuel h1 hf.1, inferTypeCore_projSlotsOk fuel h2 hf.2⟩
    | lam ty body m =>
      obtain ⟨tty, -, bt, h1, -, h2, -⟩ := inferTypeCore_lam_inv h
      rw [fvarTysOk_lam] at hf
      have hty := inferTypeCore_projSlotsOk fuel h1 hf.1
      have hb := inferTypeCore_projSlotsOk fuel h2
        (FvarTysOk.instantiate1 (fvarTysOk_fvar.mpr hty) body 0 hf.2)
      exact projSlotsOk_lam.mpr ⟨hty, ProjSlotsOk.of_instantiate1 body 0 hb⟩
    | forallE ty body m =>
      obtain ⟨tty, -, bt, -, h1, -, h2, -⟩ := inferTypeCore_forall_inv h
      rw [fvarTysOk_forallE] at hf
      have hty := inferTypeCore_projSlotsOk fuel h1 hf.1
      have hb := inferTypeCore_projSlotsOk fuel h2
        (FvarTysOk.instantiate1 (fvarTysOk_fvar.mpr hty) body 0 hf.2)
      exact projSlotsOk_forallE.mpr ⟨hty, ProjSlotsOk.of_instantiate1 body 0 hb⟩
    | letE ty v b => exact (inferTypeCore_letE_inv h).elim
    | proj sn i pe =>
      obtain ⟨tpe, -, T, -, entry, h1, -, -, hent, -, -, -, -, hT⟩ := inferTypeCore_proj_inv h
      subst hT
      exact projSlotsOk_proj.mpr
        ⟨⟨entry, hent⟩, inferTypeCore_projSlotsOk fuel h1 (fvarTysOk_proj.mp hf)⟩

/-- **No `.proj` node at an empty slot**, for a closed subject whose
full-grade inference succeeded. -/
theorem inferTypeCore_noProjAt {env : Env} {F d : Nat} {e t : Expr}
    (h : inferTypeCore mode env F d e = .ok t) (hfv : e.hasFvar = false)
    {T : Name} {i : Nat} (hslot : env.findProj? T i = none) : Expr.NoProjAt T i e :=
  ProjSlotsOk.noProjAt hslot e (inferTypeCore_projSlotsOk F h (FvarTysOk.of_not_hasFvar e hfv))

end ConLeche
