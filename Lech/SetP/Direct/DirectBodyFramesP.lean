import Lech.SetP.Direct.DirectEntryFreeP
import Lech.Verify.Direct.DirectBody

/-!
# The projection body's frame (task #175 S1)

The table stores, per field, a **body** `F_i[p⃗ ↦ bvars, f_j ↦ .proj T
j (bvar 0)]` (`directProjBodies`), and the tower law (A) reads it
through the dummy telescope `projTele (nP + 1) body`
(`Lech/Verify/ProjTele.lean`).  Two facts make the reading what the
law needs:

* **the telescope's reading is the opened body's** (`denoteP_projTele`):
  `denoteP` opens the `nP + 1` dummy binders at fresh variables, so
  the telescope reads to `mkPisAV` over `nP + 1` dummy `Sort 0` binder
  data with the body instantiated at the variables as its residual;
* **the opened body is the constructor's field domain at the frame**
  (`bodyFrames`): by `directProjBody_open` the opened body *is* the
  head domain of the constructor telescope peeled at the variables and
  the subject's earlier projections, so its reading is the field
  domain's instantiation sequence along the readings of those
  arguments (`denoteP_instPisAt_peel`), which at the frame — the
  subject a member of the family at the parameters — agrees with the
  field domain read at the subject's projection spine
  (`chainP_entry_agree`) and is graded there (the graph regime by the
  projections' fit, the squash regime by the point spine's agreement
  with a fitting prefix at every used slot, `free_of_diff`).

No annotation, inference or definitional-equality run is consumed:
the body is a substitution instance of the stored constructor type,
and the reading is a homomorphism for substitution.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The telescope's reading -/

/-- **The dummy telescope reads to the opened body**: `k` dummy
binders at depth `d` open at the variables `d, …, d + k - 1`, and the
residual is the body's instantiation sequence at them. -/
theorem denoteP_projTele {acval : Name → (Name → Nat) → AVExpr} {env : Env}
    {φ : Name → Nat} :
    ∀ (k d : Nat) (body : Expr) {RA : AVExpr},
      denoteP acval env φ (d + k)
        (Expr.instSeq ((List.range k).map fun j =>
          Expr.fvar (d + j) (.sort .zero)) (k - 1) body) = some RA →
      denoteP acval env φ d (Lech.projTele k body)
        = some (mkPisAV (List.replicate k (0, 1, .sort 0)) RA)
  | 0, d, body, RA, h => by
    simpa [Lech.projTele, Expr.instSeq, mkPisAV] using h
  | k + 1, d, body, RA, h => by
    have hspine : Expr.instSeq ((List.range (k + 1)).map fun j =>
          Expr.fvar (d + j) (.sort .zero)) (k + 1 - 1) body
        = Expr.instSeq ((List.range k).map fun j =>
            Expr.fvar (d + 1 + j) (.sort .zero)) (k - 1)
            (body.instantiate1 (Expr.fvar d (.sort .zero)) k) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
      show Expr.instSeq _ (k - 1) (body.instantiate1 _ k) = _
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      rw [show d + (j + 1) = d + 1 + j from by omega]
    rw [hspine, show d + (k + 1) = d + 1 + k from by omega] at h
    have ih := denoteP_projTele k (d + 1)
      (body.instantiate1 (Expr.fvar d (.sort .zero)) k) h
    rw [Lech.projTele, denoteP_forallE, denoteP_sort, Lech.projTele_instantiate1,
      Nat.zero_add, ih]
    rfl

/-- The telescope over the parameters and the subject, at depth `0`:
the residual is the body at the direct install's own variable
spelling (`fvsD`/`tfvD`). -/
theorem denoteP_projTele_zero {acval : Name → (Name → Nat) → AVExpr} {env : Env}
    {φ : Name → Nat} {nP : Nat} {body : Expr} {RA : AVExpr}
    (h : denoteP acval env φ (nP + 1)
      (Expr.instSpine (Lech.fvsD nP ++ [Lech.tfvD nP]) nP body) = some RA) :
    denoteP acval env φ 0 (Lech.projTele (nP + 1) body)
      = some (mkPisAV (List.replicate (nP + 1) (0, 1, .sort 0)) RA) := by
  refine denoteP_projTele (nP + 1) 0 body ?_
  rw [Nat.zero_add, Nat.add_sub_cancel]
  rw [Expr.instSpine_eq_instSeq] at h
  have e : ((List.range (nP + 1)).map fun j => Expr.fvar (0 + j) (.sort .zero))
      = Lech.fvsD nP ++ [Lech.tfvD nP] := by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    simp only [Lech.fvsD, Lech.tfvD, Nat.zero_add]
  rw [e]
  exact h

/-! ## The frame -/

omit [SetTheory V] in
theorem DomsBelow.getD_below {k : Nat} :
    ∀ {ds : List (Nat × Nat × AVExpr)} (j : Nat), DomsBelow k ds → j < ds.length →
      VExpr.bvarsBelow (k + j) (ds.getD j default).2.2.erase
  | [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | d :: ds, 0, h, _ => by simpa using h.1
  | d :: ds, j + 1, h, hj => by
    rw [List.getD_cons_succ, show k + (j + 1) = k + 1 + j from by omega]
    exact DomsBelow.getD_below j h.2 (by simpa using hj)

/-- **The opened body's frame.**  At the frame (the subject a member of
the family at the parameters — `ρ 0` in the tower over the field chain
at `ρ ∘ succ`, which satisfies the constructor's parameter context)
the opened body reads to a graded term whose value is the field
domain at the subject's projection spine.  The grading in the squash
regime rides the official guard's content (`hguard`) and the unused
earlier fields' invariance (`hfree`). -/
theorem bodyFrames {env : Env} (m : EnvS2Core V env)
    {nP nF i : Nat} {T : Name} {cty : Expr} {cds : List Expr}
    {nmC : Name} {bodyC : Expr} {mbC : BinderMeta} {body : Expr}
    (hcf : Expr.instPisAt (Lech.fvsD nP ++ Lech.projArgsD T i nP) cty
      = some (cds, .forallE
          (Expr.instSpine (Lech.fvsD nP ++ [Lech.tfvD nP]) nP body) bodyC mbC))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hprev : ∀ j, j < i → ∃ entry, env.findProj? T j = some entry)
    (hi : i < nF)
    {ds : List (Nat × Nat × AVExpr)} {bodyA : AVExpr} {ψ : Name → Nat} {w : Nat}
    (hlenDs : ds.length = nP + nF) (hbelow : DomsBelow 0 ds)
    (hctyRead0 : denoteP m.acval env ψ 0 cty = some (mkPisAV ds bodyA))
    {sorts : List Level}
    (hokB : ∀ ρ : Nat → V, Sat2 V ((ds.take nP).map (·.2.2)).reverse ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2)) ∧ FieldsValid ρ ((ds.drop nP).map (·.2.2)))
    (hbound : ∀ ρ : Nat → V, Sat2 V ((ds.take nP).map (·.2.2)).reverse ρ → w ≠ 0 →
      FieldsBound w ρ ((ds.drop nP).map (·.2.2)))
    (hsorts : ∀ ρ : Nat → V, Sat2 V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp2 V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    {used : Nat → Bool}
    (hfree : ∀ j, j < i → used j = false →
      ∃ X : AVExpr, ((ds.drop nP).map (·.2.2)).getD i default = X.liftN 1 (i - 1 - j)) :
    ∃ fdomA : AVExpr,
      denoteP m.acval env ψ (nP + 1)
        (Expr.instSpine (Lech.fvsD nP ++ [Lech.tfvD nP]) nP body) = some fdomA ∧
      ((w = 0 → ∀ j, j < i → used j = true → (sorts.getD j .zero).eval ψ = 0) →
        ∀ ρ : Nat → V,
          ρ 0 ∈ˢ towerSet w (teleOfFields (fun j => ρ (j + 1)) ((ds.drop nP).map (·.2.2))) →
          Sat2 V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
          AnnotOkP V ρ fdomA) ∧
      (∀ ρ : Nat → V,
        ρ 0 ∈ˢ towerSet w (teleOfFields (fun j => ρ (j + 1)) ((ds.drop nP).map (·.2.2))) →
        Sat2 V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
        interp2 V ρ fdomA
          = interp2 V (consList (projList i (ρ 0)) (fun j => ρ (j + 1)))
              (((ds.drop nP).map (·.2.2)).getD i default)) := by
  -- the constructor type's reading at the body's depth
  have hctyRead : denoteP m.acval env ψ (nP + 1) cty = some (mkPisAV ds bodyA) :=
    denoteP_depth_of_closed m.acval_closed hCf
      (fun k => denoteP_closed m.acval_erase m.cval_closed hCf hCb hctyRead0 1 k)
      hctyRead0 (nP + 1)
  -- the arguments' scoping
  have hlenP : (Lech.fvsD nP).length = nP := Lech.fvsD_length nP
  have hfvsDidx : ∀ (k : Nat) (x : Expr), (Lech.fvsD nP)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    have hk : k < nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1; rwa [hlenP] at this
    rw [Lech.fvsD_getElem? nP k hk] at hx
    exact ⟨.anonymous, .sort .zero, (Option.some.inj hx).symm⟩
  have hargs : ∀ a ∈ Lech.fvsD nP ++ Lech.projArgsD T i nP,
      Expr.WScoped (nP + 1) a ∧ a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      have := List.mem_range.mp hk
      refine ⟨?_, rfl⟩
      simp only [Expr.WScoped, and_true]
      omega
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
      refine ⟨?_, rfl⟩
      simp only [Expr.WScoped, Lech.tfvD, and_true]
      omega
  have hctyW : Expr.WScoped (nP + 1) cty := Expr.WScoped.of_not_hasFvar hCf
  -- the arguments' readings: the parameters and the earlier projections
  have hspP := denoteSpineP_entryParams (acval := m.acval) (env := env) (φ := ψ)
    hfvsDidx hlenP
  have hspX := denoteSpineP_entryProjs (acval := m.acval) (env := env) (φ := ψ)
    (nP := nP) (nmT := .anonymous) (sdom := .sort .zero) hprev
  have hsp : DenoteSpineP m.acval env ψ (nP + 1) (Lech.fvsD nP ++ Lech.projArgsD T i nP)
      (entryParamBvars nP ++ entryProjAVs i) :=
    DenoteSpineP.append hspP hspX
  obtain ⟨restA, hrest, hpeel⟩ := denoteP_instPisAt_peel m.acval_closed
    (acval_inst_self m) _ hcf hctyW hargs hctyRead hsp
  obtain ⟨fdomA, ba, hfdA, -, rfl⟩ := denoteP_forallE_inv hrest
  -- the peel is the instantiation sequence of the field domain
  have hlenVs : (entryParamBvars nP ++ entryProjAVs i).length = nP + i := by
    simp [entryParamBvars_length, entryProjAVs_length]
  have hsplitDs : ds = ds.take (nP + i) ++ ds.drop (nP + i) :=
    (List.take_append_drop _ _).symm
  have htele : PiTeleP (nP + i) (mkPisAV ds bodyA)
      (((ds.take (nP + i)).map (·.2.2)).reverse)
      (mkPisAV (ds.drop (nP + i)) bodyA) := by
    have h := piTeleP_mkPisAV (ds.take (nP + i)) (mkPisAV (ds.drop (nP + i)) bodyA)
    rw [← mkPisAV_append, ← hsplitDs, List.length_take, hlenDs,
      show min (nP + i) (nP + nF) = nP + i from by omega] at h
    exact h
  have hpeel' := peelPis_of_piTeleP (nP + i) htele hlenVs
  rw [hpeel] at hpeel'
  have hdropDs : ds.drop (nP + i) = ds.getD (nP + i) default :: ds.drop (nP + i + 1) := by
    rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  rw [hdropDs] at hpeel'
  simp only [mkPisAV] at hpeel'
  obtain ⟨B', hB'⟩ := instSeq_pi_dom (entryParamBvars nP ++ entryProjAVs i) (nP + i - 1)
    (ds.getD (nP + i) default).1 (ds.getD (nP + i) default).2.1
    (ds.getD (nP + i) default).2.2
    (mkPisAV (ds.drop (nP + i + 1)) bodyA)
  rw [hB'] at hpeel'
  obtain ⟨-, -, hfdomA, -⟩ := AVExpr.pi.inj (Option.some.inj hpeel')
  -- the field's domain, named
  have hFi : ((ds.drop nP).map (·.2.2)).getD i default = (ds.getD (nP + i) default).2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hFiBelow : VExpr.bvarsBelow (nP + i) (ds.getD (nP + i) default).2.2.erase := by
    have := DomsBelow.getD_below (nP + i) hbelow (by omega)
    rwa [Nat.zero_add] at this
  have hlenFs : ((ds.drop nP).map (·.2.2)).length = nF := by simp [hlenDs]
  have hlen' : (entryParamBvars nP ++ entryProjAVs i).length - 1 = nP + i - 1 := by
    rw [hlenVs]
  refine ⟨fdomA, hfdA, ?_, ?_⟩
  · -- the grading at the frame
    intro hguard ρ hx hsat
    -- the field's grading at the subject's projection spine: in the
    -- graph regime the projections fit; at a squash instance they are
    -- the point spine, which differs from a fitting prefix only at
    -- unused slots, where the field is a lift
    have hokPre : AnnotOkP V (consList (projList i (ρ 0)) (fun j => ρ (j + 1)))
        (((ds.drop nP).map (·.2.2)).getD i default) := by
      by_cases hw : w = 0
      · rw [hw] at hx
        obtain ⟨hpt, as', hfits⟩ := towerSet_zero_elim _ hx
        have hspAs := fitsS_teleOfFields.mp hfits
        obtain ⟨hpre, -⟩ := spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)
        rw [hpt, projList_pt]
        have hlenTake : (as'.take i).length = i :=
          spineFit_take_length hspAs (by rw [hlenFs]; omega)
        rw [annotOkP_congr_lifts i
          (free_of_diff hlenDs hi (hsorts _ hsat) (hguard hw) hfree hspAs)
          (consList_prefix_agree hlenTake _).2]
        exact ⟨fieldsOkB_getD (hokB _ hsat).1 (by rw [hlenFs]; exact hi) hpre,
          fieldsValid_getD (hokB _ hsat).2 (by rw [hlenFs]; exact hi) hpre⟩
      · obtain ⟨hspAll, -⟩ := towerSet_elim_teleOfFields hw hx
        obtain ⟨hpre, -⟩ := spineFit_prefix_next hspAll (by rw [hlenFs]; exact hi)
        rw [hlenFs, projList_take nF i _ (Nat.le_of_lt hi)] at hpre
        exact ⟨fieldsOkB_getD (hokB _ hsat).1 (by rw [hlenFs]; exact hi) hpre,
          fieldsValid_getD (hokB _ hsat).2 (by rw [hlenFs]; exact hi) hpre⟩
    -- the readings' gradings at the frame
    have hokArgs : ∀ w' ∈ entryParamBvars nP ++ entryProjAVs i, AnnotOkP V ρ w' := by
      intro w' hw'
      rcases List.mem_append.mp hw' with hw' | hw'
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hw'
        exact ⟨trivial, trivial⟩
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw'
        have hj' : j < i := List.mem_range.mp hj
        refine ⟨?_, projAV_validV trivial⟩
        by_cases hw0 : w = 0
        · rw [hw0] at hx
          obtain ⟨hpt, -⟩ := towerSet_zero_elim _ hx
          exact annotOk2_projAV_pt trivial (by rw [interp2_bvar, hpt])
        · exact annotOk2_projAV_tower (hbound _ hsat hw0) hx trivial (by rw [interp2_bvar])
            (by rw [hlenFs]; omega)
    rw [hfdomA, ← hlen']
    refine annotOkP_instSeq _ hokArgs ?_
    rw [(AnnotOkP_congr_below _ (nP + i) _ _ hFiBelow (chainP_entry_agree nP i ρ))]
    rw [← hFi]
    exact hokPre
  · -- the value at the frame
    intro ρ _ _
    rw [hfdomA, ← hlen', interp2_instSeq, hFi]
    exact interp2_congr_below V _ (nP + i) _ _ hFiBelow (chainP_entry_agree nP i ρ)

end Lech.SetP
