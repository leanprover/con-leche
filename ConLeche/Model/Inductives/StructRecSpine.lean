module

public import ConLeche.Model.Inductives.StructStageCtor
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitInst
public import ConLeche.Model.IndPinGrade
public section

/-!
# The recursor's frame kit (task #175 W4c, P3 module 6, part 8)

The pieces the recursor's frames are assembled from:

* `piDomsSorts_of_infer` — the per-binder domain inference *and* sort
  runs of an inferred Π-type (`piDoms_of_infer` with the sort);
* `liftN_mkPisAV` — a lifted Π-tower is the tower of lifted domains;
* `instPisAt_openerRes` — the residual of an `instPisAt` run at an
  opener spine reads to the tower's core (`instPisAt_openerDoms`'s
  companion);
* `mkAppN_okP_of_spineFit` — a graded head inhabiting a Π-tower,
  applied along a fitting spine, is graded and lands in the core;
* `famSpine_read`/`famSpine_val` — the family spine `T p⃗` at any depth
  above the parameters: its reading, its grading, and its value (the
  instantiated carrier, by `formerFold`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Lifted Π-towers -/

/-- The binder data of a lifted Π-tower: each domain lifted at its own
depth. -/
@[expose] def liftDoms (n : Nat) : Nat → List (Nat × Nat × AnnotTerm) → List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | k, d :: ds => (d.1, d.2.1, d.2.2.liftN n k) :: liftDoms n (k + 1) ds

theorem liftDoms_length (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k : Nat), (liftDoms n k ds).length = ds.length
  | [], _ => rfl
  | _ :: ds, k => by simp [liftDoms, liftDoms_length n ds (k + 1)]

theorem liftDoms_getElem? (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k i : Nat),
      (liftDoms n k ds)[i]? = ds[i]?.map fun d => (d.1, d.2.1, d.2.2.liftN n (k + i))
  | [], _, _ => rfl
  | _ :: ds, k, 0 => by simp [liftDoms]
  | _ :: ds, k, i + 1 => by
    simp only [liftDoms, List.getElem?_cons_succ, liftDoms_getElem? n ds (k + 1) i]
    rw [show k + 1 + i = k + (i + 1) from by omega]

theorem liftN_mkPisAV (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm) (k : Nat),
      (mkPisAV ds b).liftN n k = mkPisAV (liftDoms n k ds) (b.liftN n (k + ds.length))
  | [], b, k => by simp [mkPisAV, liftDoms]
  | d :: ds, b, k => by
    simp only [mkPisAV, liftDoms, AnnotTerm.liftN_pi, liftN_mkPisAV n ds b (k + 1),
      List.length_cons]
    rw [show k + 1 + ds.length = k + (ds.length + 1) from by omega]

theorem stripPisAV_mkPisAV_take :
    ∀ (n : Nat) (ds : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm), n ≤ ds.length →
      stripPisAV n (mkPisAV ds b) = some (ds.take n, mkPisAV (ds.drop n) b)
  | 0, _, _, _ => rfl
  | n + 1, [], _, h => by simp at h
  | n + 1, d :: ds, b, h => by
    simp only [mkPisAV, stripPisAV, List.take_succ_cons, List.drop_succ_cons,
      stripPisAV_mkPisAV_take n ds b (by simpa using h), Option.map_some]

/-! ## Graded applications along a fit -/

/-- A fit of bounded domains reads the same at any frame agreeing
below the cut. -/
theorem spineFit_congr_below :
    ∀ {pds : List (Nat × Nat × AnnotTerm)} {k : Nat} {ρ ρ' : Nat → V} {as : List V},
      DomsBelow k pds → (∀ i, i < k → ρ i = ρ' i) →
      SpineFit ρ (pds.map (·.2.2)) as → SpineFit ρ' (pds.map (·.2.2)) as
  | [], _, _, _, [], _, _, h => h
  | [], _, _, _, _ :: _, _, _, h => h.elim
  | _ :: _, _, _, _, [], _, _, h => h.elim
  | d :: pds, k, ρ, ρ', a :: as, hb, hρ, h => by
    simp only [List.map_cons, SpineFit] at h ⊢
    refine ⟨?_, spineFit_congr_below hb.2 (fun i hi => ?_) h.2⟩
    · rw [← interp_congr_below V d.2.2 k ρ ρ' hb.1 hρ]; exact h.1
    · cases i with
      | zero => rfl
      | succ i => exact hρ i (by omega)

/-! ## The family spine above the parameters -/

/-- The parameter variables as seen from depth `D` (`D ≥ nP`). -/
@[expose] def paramBvarsAt (nP D : Nat) : List AnnotTerm :=
  (List.range nP).map fun k => .bvar (D - 1 - k)

theorem paramBvars_eq_paramBvarsAt (nP nF : Nat) :
    paramBvars nP nF = paramBvarsAt nP (nP + nF) := rfl

/-- A same-index `fvar` spine reads to the parameter variables. -/
theorem denoteMetaSpine_fvars {acval : Name → (Name → Nat) → AnnotTerm} (D : Nat) :
    ∀ (fvs : List Expr) (k₀ : Nat),
      (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar (k₀ + k) ty) →
      DenoteMetaSpine acval env φ D fvs
        ((List.range fvs.length).map fun k => .bvar (D - 1 - (k₀ + k)))
  | [], _, _ => .nil
  | x :: fvs, k₀, hidx => by
    obtain ⟨nm, ty, rfl⟩ := hidx 0 x rfl
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine .cons (by rw [denoteMeta_fvar, Nat.add_zero]) ?_
    have := denoteMetaSpine_fvars (acval := acval) D fvs (k₀ + 1)
      (fun k y hy => by
        obtain ⟨ty', h⟩ := hidx (k + 1) y (by simpa using hy)
        exact ⟨ty', by rw [h]; congr 1; omega⟩)
    have hmapeq : (List.map ((fun k => AnnotTerm.bvar (D - 1 - (k₀ + k))) ∘ Nat.succ)
          (List.range fvs.length))
        = (List.range fvs.length).map fun k => AnnotTerm.bvar (D - 1 - (k₀ + 1 + k)) := by
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_def]
      congr 1
      omega
    rw [hmapeq]
    exact this

theorem map_paramBvarsAt_interp {nP e : Nat} {ρp σ : Nat → V}
    (hσ : ∀ j, σ (j + e) = ρp j) :
    (paramBvarsAt nP (nP + e)).map (interp V σ) = (List.range nP).reverse.map ρp := by
  apply List.ext_getElem
  · simp [paramBvarsAt]
  · intro i h1 h2
    simp only [paramBvarsAt, List.getElem_map, List.getElem_range, interp_bvar,
      List.getElem_reverse, List.length_range]
    rw [← hσ]
    congr 1
    have : i < nP := by simpa [paramBvarsAt] using h1
    omega
