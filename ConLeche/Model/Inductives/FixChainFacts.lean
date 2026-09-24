module

import ConLeche.Model.Inductives.FixChains
public import ConLeche.Model.Inductives.BlockData
public section

/-!
# The former's index telescope (task #188)

The former's index telescope graded and bounded at the parameter frame
(`idxOk_of`): the index binders' sorts the install read
(`checkStructFieldSortsI` at the former's opened telescope), joined
into the tuple universe `idxUniv`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Kit -/

/-- The tuple universe: the join of the index binders' sorts. -/
def idxUniv (ψ : Name → Nat) (isorts : List Level) : Nat :=
  (isorts.map (Level.eval ψ)).foldl max 0

omit [SetTheory V] in
theorem le_foldl_max : ∀ (l : List Nat) (a x : Nat), x ∈ l → x ≤ l.foldl max a
  | [], _, _, h => nomatch h
  | y :: l, a, x, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a x) (foldl_max_ge l _)
    · exact le_foldl_max l (max a y) x h
where
  foldl_max_ge : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
    | [], _ => Nat.le_refl _
    | y :: l, a => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left a y) (foldl_max_ge l _)

omit [SetTheory V] in
theorem eval_le_idxUniv {ψ : Name → Nat} {isorts : List Level} {j : Nat} {s : Level}
    (h : isorts[j]? = some s) : s.eval ψ ≤ idxUniv ψ isorts :=
  le_foldl_max _ 0 _ (List.mem_map.mpr ⟨s, List.mem_of_getElem? h, rfl⟩)

/-! ## The index telescope -/

/-- **The former's index telescope**, graded and bounded by the tuple
universe at every parameter frame. -/
theorem idxOk_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {nP nIdx : Nat} {resSort : Level} {cvTa : ConstantVal} {T : Name}
    {caps : IndCaps} (hfT : env.find? T = some (.indInfo cvTa caps))
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars (nP + nIdx) cvTa.type 0 = some (tfvs, trest))
    {isorts : List Level}
    (hsorts : ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F) env true false resSort nP
      (tfvs.drop nP) [] nIdx = .ok isorts)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hρp : Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρp) :
    IdxOk (idxUniv ψ isorts) ρp (((ppsAll ψ).drop nP).map (·.2.2)) := by
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  have hT : Opened mp.base2 ψ (nP + nIdx) cvTa.type tfvs trest
      (((ppsAll ψ).map (·.2.2)).reverse) (.sort (resSort.eval ψ)) :=
    opened_of_peel hopT hTf hTb (hFD.read ψ) (hFD.len ψ) (hFD.okTy ψ)
  have hc := claimsAt_of hμ mp ψ F
  obtain ⟨-, hrows⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
  have hlenT : tfvs.length = nP + nIdx := openPisAtFvars_length _ hopT
  have hΓ : (((ppsAll ψ).map (·.2.2)).reverse).length = nP + nIdx := by simp [hFD.len ψ]
  -- the index binders' universes at their frames
  have hbnd : ∀ j, j < nIdx → ∀ ρ : Nat → V,
      Sat V ((((ppsAll ψ).map (·.2.2)).reverse).drop (nP + nIdx - (nP + j))) ρ →
      interp V ρ ((((ppsAll ψ).map (·.2.2)).reverse).getD (nP + nIdx - 1 - (nP + j)) default)
        ∈ˢ (univ (idxUniv ψ isorts) : V) := by
    intro j hj ρ hρ
    obtain ⟨fv, ty, u, hfv, hu, hi, hens, -, -⟩ := hrows j hj
    have hfvT : tfvs[nP + j]? = some fv := by
      rw [List.getElem?_drop] at hfv; exact hfv
    obtain ⟨-, hws, hb, hL, hleaf⟩ := hT.var (nP + j) fv hfvT
    have hCtx := hT.ctx (i := nP + j) (by omega) hws hleaf
    have hread := hT.doms (nP + j) fv hfvT
    have hrow := hc.sortRow hi hens hws hb hL hCtx hread ρ hρ
    exact univ_mono (eval_le_idxUniv (ψ := ψ) hu) _ hrow.2
  have hρp' : Sat V ((((ppsAll ψ).map (·.2.2)).reverse).drop (nP + nIdx - (nP + 0))) ρp := by
    rw [Nat.add_zero, drop_fields_eq (hFD.len ψ) nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
    exact hρp
  have hok := fieldsOkB_of_frame rfl hΓ hT.okΓ (fun j hj ρ hρ _ => hbnd j hj ρ hρ) 0 (Nat.zero_le _)
    ρp hρp'
  have hbd := fieldsBound_of_frame rfl hΓ hbnd 0 (Nat.zero_le _) ρp hρp'
  rw [fieldsFrom_eq_drop (hFD.len ψ)] at hok hbd
  exact ⟨hok, hbd⟩

end ConLeche.Model
