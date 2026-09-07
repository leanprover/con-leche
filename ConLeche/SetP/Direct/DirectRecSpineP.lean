import ConLeche.SetP.Direct.DirectStageCtorP
import ConLeche.SetP.IndProjKitP

/-!
# The recursor's frame kit (task #175 W4c, P3 module 6, part 8)

The pieces the recursor's frames are assembled from:

* `piDomsSorts_of_infer` — the per-binder domain inference *and* sort
  runs of an inferred Π-type (`piDoms_of_infer` with the sort);
* `liftN_mkPisAV` — a lifted Π-tower is the tower of lifted domains;
* `instPisAt_openerResP` — the residual of an `instPisAt` run at an
  opener spine reads to the tower's core (`instPisAt_openerDomsP`'s
  companion);
* `mkAppN_okP_of_spineFit` — a graded head inhabiting a Π-tower,
  applied along a fitting spine, is graded and lands in the core;
* `famSpine_read`/`famSpine_val` — the family spine `T p⃗` at any depth
  above the parameters: its reading, its grading, and its value (the
  instantiated carrier, by `formerFold`).
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AVExpr)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Inference kit -/

/-! ## Lifted Π-towers -/

/-- The binder data of a lifted Π-tower: each domain lifted at its own
depth. -/
def liftDoms (n : Nat) : Nat → List (Nat × Nat × AVExpr) → List (Nat × Nat × AVExpr)
  | _, [] => []
  | k, d :: ds => (d.1, d.2.1, d.2.2.liftN n k) :: liftDoms n (k + 1) ds

theorem liftDoms_length (n : Nat) :
    ∀ (ds : List (Nat × Nat × AVExpr)) (k : Nat), (liftDoms n k ds).length = ds.length
  | [], _ => rfl
  | _ :: ds, k => by simp [liftDoms, liftDoms_length n ds (k + 1)]

theorem liftDoms_getElem? (n : Nat) :
    ∀ (ds : List (Nat × Nat × AVExpr)) (k i : Nat),
      (liftDoms n k ds)[i]? = ds[i]?.map fun d => (d.1, d.2.1, d.2.2.liftN n (k + i))
  | [], _, _ => rfl
  | _ :: ds, k, 0 => by simp [liftDoms]
  | _ :: ds, k, i + 1 => by
    simp only [liftDoms, List.getElem?_cons_succ, liftDoms_getElem? n ds (k + 1) i]
    rw [show k + 1 + i = k + (i + 1) from by omega]

theorem liftN_mkPisAV (n : Nat) :
    ∀ (ds : List (Nat × Nat × AVExpr)) (b : AVExpr) (k : Nat),
      (mkPisAV ds b).liftN n k = mkPisAV (liftDoms n k ds) (b.liftN n (k + ds.length))
  | [], b, k => by simp [mkPisAV, liftDoms]
  | d :: ds, b, k => by
    simp only [mkPisAV, liftDoms, AVExpr.liftN_pi, liftN_mkPisAV n ds b (k + 1),
      List.length_cons]
    rw [show k + 1 + ds.length = k + (ds.length + 1) from by omega]

theorem stripPisAV_mkPisAV_take :
    ∀ (n : Nat) (ds : List (Nat × Nat × AVExpr)) (b : AVExpr), n ≤ ds.length →
      stripPisAV n (mkPisAV ds b) = some (ds.take n, mkPisAV (ds.drop n) b)
  | 0, _, _, _ => rfl
  | n + 1, [], _, h => by simp at h
  | n + 1, d :: ds, b, h => by
    simp only [mkPisAV, stripPisAV, List.take_succ_cons, List.drop_succ_cons,
      stripPisAV_mkPisAV_take n ds b (by simpa using h), Option.map_some]

/-! ## The residual of an `instPisAt` run at openers -/

/-- **The residual reads to the tower's core** (`instPisAt_openerDomsP`'s
companion): at an opener spine the run instantiates with the very
`fvar`s the reading opens with. -/
theorem instPisAt_openerResP {acval : Name → (Name → Nat) → AVExpr} :
    ∀ (sp : List Expr) {ty : Expr} {ds : List Expr} {rs : Expr},
      Expr.instPisAt sp ty = some (ds, rs) →
      ∀ {j : Nat} {T : AVExpr},
        (∀ (q : Nat) (x : Expr), sp[q]? = some x →
          ∃ t, x = Expr.fvar (j + q) t) →
        denoteP acval env φ j ty = some T →
        ∀ {Γ : List AVExpr} {R : AVExpr}, PiTeleP sp.length T Γ R →
          denoteP acval env φ (j + sp.length) rs = some R := by
  intro sp
  induction sp with
  | nil =>
    intro ty ds rs h j T _ hT Γ R htele
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases htele
    exact hT
  | cons a sp ih =>
    intro ty ds rs h j T hshape hT Γ R htele
    obtain ⟨t0, rfl⟩ := hshape 0 a rfl
    match ty, h with
    | .forallE dom bodyE mb, h =>
      simp only [Expr.instPisAt] at h
      cases h1 : Expr.instPisAt sp (bodyE.instantiate1 (.fvar (j + 0) t0)) with
      | none => rw [h1] at h; exact nomatch h
      | some p => ?_
      rw [h1] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨A, Bv, -, hB, rfl⟩ := denoteP_forallE_inv hT
      obtain ⟨u', v', A', B', Γ', heqT, rfl, htele'⟩ := htele.succ_inv
      obtain ⟨rfl, rfl⟩ : A' = A ∧ B' = Bv := by
        injection heqT with _ _ hA' hB'
        exact ⟨hA'.symm, hB'.symm⟩
      have hB' : denoteP acval env φ (j + 1)
          (bodyE.instantiate1 (.fvar (j + 0) t0)) = some B' := by
        rw [denoteP_erasedEq (ConLeche.Expr.ErasedEq.instantiate1
          (ConLeche.Expr.ErasedEq.rfl bodyE)
          (show ConLeche.Expr.ErasedEq (.fvar (j + 0) t0) (.fvar j dom) from by
            rw [Nat.add_zero]; constructor)) (j + 1)]
        exact hB
      have hshape' : ∀ (q0 : Nat) (x : Expr), sp[q0]? = some x →
          ∃ t, x = Expr.fvar (j + 1 + q0) t := by
        intro q0 x hx
        obtain ⟨t', hx'⟩ := hshape (q0 + 1) x (by simpa using hx)
        exact ⟨t', by rw [hx']; congr 1; omega⟩
      have := ih h1 hshape' hB' htele'
      simp only [List.length_cons]
      rw [show j + (sp.length + 1) = j + 1 + sp.length from by omega]
      exact this
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.instPisAt] at h

/-! ## Graded applications along a fit -/

/-- A fit of bounded domains reads the same at any frame agreeing
below the cut. -/
theorem spineFit_congr_below :
    ∀ {pds : List (Nat × Nat × AVExpr)} {k : Nat} {ρ ρ' : Nat → V} {as : List V},
      DomsBelow k pds → (∀ i, i < k → ρ i = ρ' i) →
      SpineFit ρ (pds.map (·.2.2)) as → SpineFit ρ' (pds.map (·.2.2)) as
  | [], _, _, _, [], _, _, h => h
  | [], _, _, _, _ :: _, _, _, h => h.elim
  | _ :: _, _, _, _, [], _, _, h => h.elim
  | d :: pds, k, ρ, ρ', a :: as, hb, hρ, h => by
    simp only [List.map_cons, SpineFit] at h ⊢
    refine ⟨?_, spineFit_congr_below hb.2 (fun i hi => ?_) h.2⟩
    · rw [← interp2_congr_below V d.2.2 k ρ ρ' hb.1 hρ]; exact h.1
    · cases i with
      | zero => rfl
      | succ i => exact hρ i (by omega)

/-! ## The family spine above the parameters -/

/-- The parameter variables as seen from depth `D` (`D ≥ nP`). -/
def paramBvarsAt (nP D : Nat) : List AVExpr :=
  (List.range nP).map fun k => .bvar (D - 1 - k)

theorem paramBvars_eq_paramBvarsAt (nP nF : Nat) :
    paramBvars nP nF = paramBvarsAt nP (nP + nF) := rfl

/-- A same-index `fvar` spine reads to the parameter variables. -/
theorem denoteSpineP_fvars {acval : Name → (Name → Nat) → AVExpr} (D : Nat) :
    ∀ (fvs : List Expr) (k₀ : Nat),
      (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar (k₀ + k) ty) →
      DenoteSpineP acval env φ D fvs
        ((List.range fvs.length).map fun k => .bvar (D - 1 - (k₀ + k)))
  | [], _, _ => .nil
  | x :: fvs, k₀, hidx => by
    obtain ⟨nm, ty, rfl⟩ := hidx 0 x rfl
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine .cons (by rw [denoteP_fvar, Nat.add_zero]) ?_
    have := denoteSpineP_fvars (acval := acval) D fvs (k₀ + 1)
      (fun k y hy => by
        obtain ⟨ty', h⟩ := hidx (k + 1) y (by simpa using hy)
        exact ⟨ty', by rw [h]; congr 1; omega⟩)
    have hmapeq : (List.map ((fun k => AVExpr.bvar (D - 1 - (k₀ + k))) ∘ Nat.succ)
          (List.range fvs.length))
        = (List.range fvs.length).map fun k => AVExpr.bvar (D - 1 - (k₀ + 1 + k)) := by
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_def]
      congr 1
      omega
    rw [hmapeq]
    exact this

theorem map_paramBvarsAt_interp {nP e : Nat} {ρp σ : Nat → V}
    (hσ : ∀ j, σ (j + e) = ρp j) :
    (paramBvarsAt nP (nP + e)).map (interp2 V σ) = (List.range nP).reverse.map ρp := by
  apply List.ext_getElem
  · simp [paramBvarsAt]
  · intro i h1 h2
    simp only [paramBvarsAt, List.getElem_map, List.getElem_range, interp2_bvar,
      List.getElem_reverse, List.length_range]
    rw [← hσ]
    congr 1
    have : i < nP := by simpa [paramBvarsAt] using h1
    omega
