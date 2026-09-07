import Lech.SetP.Direct.DirectRecDataP
import Lech.SetP.IndProjKitP

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

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Inference kit -/

theorem ensureSortCore_of_whnf {F d : Nat} {t : Expr} {u : Level}
    (h : Lech.whnf μ env F d t = .ok (.sort u)) :
    Lech.ensureSortCore μ env F d t = .ok u := by
  unfold Lech.ensureSortCore Lech.ensureSort
  simp only [Bind.bind, Except.bind, Lech.whnf_def]
  rw [h]
  exact rfl

/-- **The Π-prefix's domain runs, with their sorts.** -/
theorem piDomsSorts_of_infer :
    ∀ (n : Nat) {F d : Nat} {e t : Expr} {fvs : List Expr} {opened : Expr},
      openPisAtFvars n e d = some (fvs, opened) →
      Lech.inferTypeCore μ env F d e = .ok t →
      ∀ (j : Nat) (x : Expr), fvs[j]? = some x →
        ∃ (F' : Nat) (tj : Expr) (u : Level),
          Lech.inferTypeCore μ env F' (d + j) (Expr.fvarTypeD x) = .ok tj ∧
          Lech.ensureSortCore μ env F' (d + j) tj = .ok u
  | 0, F, d, e, t, fvs, opened, hop, _, j, x, hx => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact nomatch hx
  | n + 1, F, d, e, t, fvs, opened, hop, h, j, x, hx => by
    match e, hop, h with
    | .forallE dom body mb, hop, h =>
      match F, h with
      | 0, h => rw [Lech.inferTypeCore_zero] at h; exact nomatch h
      | F + 1, h =>
        obtain ⟨tty, u, bt, v, hty, hwh, hbt, -, -, rfl⟩ :=
          Lech.inferTypeCore_forall_inv h
        simp only [openPisAtFvars] at hop
        split at hop
        · next fvs' e' hop' =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop
          cases j with
          | zero =>
            obtain rfl : Expr.fvar d dom = x := by simpa using hx
            exact ⟨F, tty, u, by rw [Nat.add_zero]; exact hty,
              by rw [Nat.add_zero]; exact ensureSortCore_of_whnf hwh⟩
          | succ j =>
            simp only [List.getElem?_cons_succ] at hx
            obtain ⟨F', tj, u', hj, hu'⟩ := piDomsSorts_of_infer n hop' hbt j x hx
            exact ⟨F', tj, u', by rw [show d + (j + 1) = d + 1 + j from by omega]; exact hj,
              by rw [show d + (j + 1) = d + 1 + j from by omega]; exact hu'⟩
        · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _, hop, _ | .sort _, hop, _
    | .const _ _, hop, _ | .app _ _, hop, _ | .lam _ _ _, hop, _
    | .letE _ _ _, hop, _ | .lit _, hop, _ | .proj _ _ _, hop, _ =>
      simp [openPisAtFvars] at hop

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

theorem liftDoms_mem (n : Nat) :
    ∀ {ds : List (Nat × Nat × AVExpr)} {k : Nat} {d : Nat × Nat × AVExpr},
      d ∈ liftDoms n k ds → ∃ d' ∈ ds, d.1 = d'.1 ∧ d.2.1 = d'.2.1
  | [], _, _, h => nomatch h
  | d₀ :: ds, k, d, h => by
    simp only [liftDoms, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨d₀, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨d', hd', h1, h2⟩ := liftDoms_mem n h
      exact ⟨d', List.mem_cons_of_mem _ hd', h1, h2⟩

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
        rw [denoteP_erasedEq (Lech.Expr.ErasedEq.instantiate1
          (Lech.Expr.ErasedEq.rfl bodyE)
          (show Lech.Expr.ErasedEq (.fvar (j + 0) t0) (.fvar j dom) from by
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

/-- **A graded head inhabiting a Π-tower (bits nonzero), applied along
a fitting spine, is graded and lands in the core** — the type's frame
`σ` and the spine's `ρ` kept apart, as the fit peels by `cons`. -/
theorem mkAppN_okP_of_spineFit :
    ∀ {pds : List (Nat × Nat × AVExpr)} {b f : AVExpr} {args : List AVExpr}
      {ρ σ : Nat → V},
      (∀ d ∈ pds, d.2.1 ≠ 0) → AnnotOkP V ρ f → (∀ a ∈ args, AnnotOkP V ρ a) →
      interp2 V ρ f ∈ˢ interp2 V σ (mkPisAV pds b) →
      SpineFit σ (pds.map (·.2.2)) (args.map (interp2 V ρ)) →
      AnnotOkP V ρ (AVExpr.mkAppN f args) ∧
        interp2 V ρ (AVExpr.mkAppN f args)
          ∈ˢ interp2 V (consList (args.map (interp2 V ρ)) σ) b
  | [], _, _, [], _, _, _, hf, _, hmem, _ => ⟨hf, hmem⟩
  | [], _, _, _ :: _, _, _, _, _, _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, _, _, _, _, _, hsp => hsp.elim
  | d :: pds, b, f, a :: args, ρ, σ, hnz, hf, hargs, hmem, hsp => by
    simp only [List.map_cons, SpineFit] at hsp
    simp only [mkPisAV, interp2_pi] at hmem
    rw [AVExpr.mkAppN_cons, List.map_cons, consList_cons]
    have ha := hargs a List.mem_cons_self
    refine mkAppN_okP_of_spineFit (fun d' hd' => hnz d' (List.mem_cons_of_mem _ hd'))
      ⟨?_, ?_⟩ (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha')) ?_ hsp.2
    · rw [AnnotOk2_app]
      exact ⟨hf.1, ha.1, d.2.1, interp2 V σ d.2.2,
        fun x => interp2 V (cons x σ) (mkPisAV pds b), hmem, hsp.1,
        fun h0 => absurd h0 (hnz d List.mem_cons_self)⟩
    · rw [AnnotValidV_app]; exact ⟨hf.2, ha.2⟩
    · rw [interp2_app]
      exact app_mem_piR_pos (hnz d List.mem_cons_self) hmem hsp.1

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

/-- **The family spine's reading**: `T p⃗` at depth `D` reads to the
former's leaf applied to the parameter variables. -/
theorem famSpine_read {m : EnvS2Core V env} {T : Name} {lps : List Name}
    {ci : ConstantInfo} (hfT : env.find? T = some ci)
    (hlps : ci.toConstantVal.levelParams = lps)
    {fvs : List Expr} {nP : Nat} (hlen : fvs.length = nP)
    (hidx : ∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (D : Nat) (ψ : Name → Nat) :
    denoteP m.acval env ψ D (Expr.mkAppN (.const T (lps.map .param)) fvs)
      = some (AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP D)) := by
  have hsp := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) D fvs 0
    (fun k x hx => by obtain ⟨ty, h⟩ := hidx k x hx; exact ⟨ty, by rw [h, Nat.zero_add]⟩)
  simp only [Nat.zero_add, hlen] at hsp
  refine denoteP_mkAppN hsp ?_
  rw [denoteP_const hfT (by rw [hlps]; simp), hlps, Level.substFn_param_self]

/-- `famSpine_read` at any level instantiation fixed by the valuation
(task #175 W4c P3 module 7; the guard's zeroing instantiation it
served retired with the per-slot entry stage at task #175 S1). -/
theorem famSpine_read_at {m : EnvS2Core V env} {T : Name} {lps : List Name}
    {ci : ConstantInfo} (hfT : env.find? T = some ci)
    (hlps : ci.toConstantVal.levelParams = lps)
    {us : List Level} {ψ : Name → Nat}
    (hus : Level.substFn ψ lps us = ψ) (hlus : us.length = lps.length)
    {fvs : List Expr} {nP : Nat} (hlen : fvs.length = nP)
    (hidx : ∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (D : Nat) :
    denoteP m.acval env ψ D (Expr.mkAppN (.const T us) fvs)
      = some (AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP D)) := by
  have hsp := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) D fvs 0
    (fun k x hx => by obtain ⟨ty, h⟩ := hidx k x hx; exact ⟨ty, by rw [h, Nat.zero_add]⟩)
  simp only [Nat.zero_add, hlen] at hsp
  refine denoteP_mkAppN hsp ?_
  rw [denoteP_const hfT (by rw [hlps]; exact hlus), hlps, hus]

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

/-- **The family spine's value and grading** at any frame `σ` whose
`e`-th tail is a parameter valuation: the instantiated carrier
(`formerFold`), graded (`mkAppN_okP_of_spineFit`). -/
theorem famSpine_val {w : Nat} {Fs : List AVExpr}
    {pps : List (Nat × Nat × AVExpr)} {nP : Nat}
    (hbits : ∀ d ∈ pps, d.2.1 ≠ 0) (hbelow : DomsBelow 0 pps) (hlen : pps.length = nP)
    (hok : ∀ ρ : Nat → V, ParamsOkT w ρ Fs pps)
    (hval : ∀ ρ : Nat → V, UnderTowerValid ρ (towerBodyAV w Fs) pps)
    (hcl : VExpr.bvarsBelow 0 (directTyAV w pps Fs).erase)
    {ρp σ : Nat → V} {e : Nat} (hσ : ∀ j, σ (j + e) = ρp j)
    (hsat : Sat2 V ((pps.map (·.2.2)).reverse) ρp) :
    AnnotOkP V σ (AVExpr.mkAppN (directTyAV w pps Fs) (paramBvarsAt nP (nP + e))) ∧
      interp2 V σ (AVExpr.mkAppN (directTyAV w pps Fs) (paramBvarsAt nP (nP + e)))
        = towerSet w (teleOfFields ρp Fs) := by
  have hspP := spineFit_of_sat2 (Δ₀ := []) (Ds := pps.map (·.2.2))
    (by rw [List.append_nil]; exact hsat)
  simp only [List.length_map, hlen] at hspP
  have hmap := map_paramBvarsAt_interp (V := V) (nP := nP) hσ
  -- the fit, at the application's own frame
  have hspσ : SpineFit σ (pps.map (·.2.2)) ((paramBvarsAt nP (nP + e)).map (interp2 V σ)) := by
    rw [hmap]
    exact spineFit_congr_below hbelow (fun i hi => absurd hi (Nat.not_lt_zero i)) hspP
  refine ⟨(mkAppN_okP_of_spineFit (b := .sort w) hbits (directTyAV_okP (hok σ) (hval σ))
    (fun a ha => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
      exact ⟨by rw [AnnotOk2_bvar]; trivial, by rw [AnnotValidV_bvar]; trivial⟩)
    (directTyAV_mem (hok σ)) hspσ).1, ?_⟩
  -- the value: the former's fold along the parameters
  rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V σ) (g := SetTheory.app), hmap,
    interp2_closed (V := V) hcl σ (fun j => ρp (j + nP)), formerFold (hok _) hspP,
    consList_range_reverse]
