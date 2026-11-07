module

import ConLeche.Verify.PropWhen
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.ProjGuard
import ConLeche.Model.OpenedCtx
import ConLeche.Model.CtxOkKit
public import ConLeche.Model.Rules.Inputs

public section

/-!
# A projection's guard, read at its use (task #480)

The rows of `projGuardRows` are the constructor's domains at the use's
levels, opened at the telescope's own variables.  Each row's derivation
(`GuardRows`) says its term has, at the environment of the use, a type
reducing to `Prop`; read through the rule soundness at that environment,
the domain is a proposition at every valuation satisfying the earlier
domains (`TowerGuardAt`).  Nothing here relates the use to the structure's
install: the typing law's premise is established here, at the use.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal ProjEntry)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- The rows' relation's motive, its empty list. -/
theorem GuardRows.nil_sound {guardSort : Level} : GuardRowsSem m φ guardSort [] := fun _ h => nomatch h

/-- The rows' relation's motive, one more row. -/
theorem GuardRows.row_sound {guardSort : Level} {d : Nat} {dom t : Expr} {u : Level}
    {rest : List (Nat × Expr)}
    (hi : InferSemIO m φ d dom t) (hr : RedSem m φ d t (.sort u)) (hrr : Red env d t (.sort u))
    (hz : Level.zeroWhereZero guardSort u = true) (hrest : GuardRowsSem m φ guardSort rest) :
    GuardRowsSem m φ guardSort ((d, dom) :: rest) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨t, u, hi, hr, hrr, hz⟩
  · exact hrest p hp

/-- Dropping from the reverse of a list of length `k` leaves the reverse of
a prefix. -/
theorem reverse_drop_eq {α : Type _} (l : List α) {k i : Nat} (hl : l.length = k) :
    l.reverse.drop (k - i) = (l.take i).reverse := by
  conv => lhs; rw [← List.take_append_drop i l, List.reverse_append]
  have h : (l.drop i).reverse.length = k - i := by simp [hl]
  rw [← h, List.drop_left]

/-- **The rows of the typing law's premise, from the use's derivations.** -/
theorem rowsAt_of_rows (hin : RulesInputs V m φ) {entry : ProjEntry} {us : List Level}
    {rows : List (Nat × Expr)} {cvC : ConstantVal} {nP nF : Nat} {guardSort : Level}
    (hfC : env.find? entry.ctor = some (.ctorInfo cvC nP nF))
    (hus : us.length = cvC.levelParams.length)
    (hrows : projGuardRows env.find? entry us = some rows)
    (hg : GuardRowsSem m φ guardSort rows) (hzero : guardSort.eval φ = 0) :
    RowsAt m φ entry us cvC 0 := by
  intro ds b hread hlt j hj hrow ρ hsat
  have hwfC := m.wf.consts _ (ConLeche.Env.find?_mem hfC)
  have hcl : (cvC.type.instantiateLevelParams cvC.levelParams us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwfC.1
  have hbd : (cvC.type.instantiateLevelParams cvC.levelParams us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hwfC.2.2.2.1
  -- the rows' shape
  unfold ConLeche.projGuardRows at hrows
  rw [hfC] at hrows
  simp only [ConstantInfo.toConstantVal] at hrows
  split at hrows
  case h_2 => exact nomatch hrows
  rename_i fvsP r hp
  -- the row, at the telescope opened through the projected field
  obtain ⟨fvs, o, hop, hcomplete⟩ := ConLeche.projGuardRows_complete hbd hp hrows
  obtain ⟨x, hx, hmem⟩ := hcomplete j hj hrow
  -- the opening, read
  have hk : entry.numParams + entry.idx + 1 ≤ ds.length := hlt
  obtain ⟨pps, b', hst, -, hlenp, hbind⟩ := denote_openPis _ hop hread
  rw [stripPisAV_mkPisAV_take _ ds b hk] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst).symm
  have hlenF : fvs.length = entry.numParams + entry.idx + 1 := openPisAtFvars_length _ hop
  obtain ⟨t, u, hsem, hred, hrr, hz⟩ := hg _ hmem
  -- the telescope's grading
  obtain ⟨ta, hta, hokT, -⟩ := hin.const_ty 0 entry.ctor _ us hfC hus
  obtain rfl : ta = mkPisAV ds b := Option.some.inj (hta.symm.trans hread)
  have hdoms := mkPisAV_doms_graded (V := V) (b := b) ds (Δ₀ := []) (fun ρ _ => (hokT ρ).1)
  -- the opened context
  have hlenΓ : (ds.take (entry.numParams + entry.idx + 1)).reverse.length
      = entry.numParams + entry.idx + 1 := by simp; omega
  have hgetΓ : ∀ {i : Nat}, i < entry.numParams + entry.idx + 1 →
      (ds.take (entry.numParams + entry.idx + 1)).reverse.getD
        (entry.numParams + entry.idx + 1 - 1 - i) default = ds.getD i default := by
    intro i hi
    have hlt' : i < ds.length := by omega
    refine getD_reverse_of_peel (by simp; omega) hi ?_
    rw [List.getElem?_take_of_lt hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt', Option.getD_some]
  have hdropΓ : ∀ {i : Nat}, i ≤ entry.numParams + entry.idx + 1 →
      (ds.take (entry.numParams + entry.idx + 1)).reverse.drop
        (entry.numParams + entry.idx + 1 - i) = (ds.take i).reverse := by
    intro i hi
    rw [reverse_drop_eq _ (by simp; omega), List.take_take, Nat.min_eq_left hi]
  have hi0 : entry.numParams + j < entry.numParams + entry.idx + 1 := by omega
  have hnil := ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl
  have hopener : ∀ l ∈ x.fvarTypeD.fvarLeaves, ConLeche.Expr.fvar l.1 l.2 ∈ fvs := by
    intro l hl
    have hmemx : x ∈ fvs := List.mem_of_getElem? hx
    obtain ⟨ty, hty⟩ := openPisAtFvars_index _ _ 0 hop _ x hx
    have hlx : l ∈ x.fvarLeaves := by
      subst hty
      simp only [Expr.fvarTypeD] at hl
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hl
    rcases openPisAtFvars_leaves _ hop l (Or.inr ⟨x, hmemx, hlx⟩) with h | h
    · rw [hnil] at h; exact absurd h List.not_mem_nil
    · exact h
  have hwx : Expr.WScoped (entry.numParams + j) x.fvarTypeD := by
    have := openPisAtFvars_typeWScoped _ hop (Expr.WScoped.of_not_hasFvar hcl) _ x hx
    simpa using this
  have hbF := (openPisAtFvars_bounded _ hop hbd).2
  have hbx := hbF x (List.mem_of_getElem? hx)
  have hLx : Expr.LeavesBounded x.fvarTypeD := by
    intro l hl
    have := hbF _ (hopener l hl)
    simpa [Expr.fvarTypeD] using this
  have hC : CtxOk m φ (entry.numParams + j) (ds.take (entry.numParams + j)).reverse
      x.fvarTypeD := by
    have := ctxOk_opened (m := m) (φ := φ) hop hcl hlenΓ
      (fun i y hy => by
        obtain ⟨p, hp, hd⟩ := hbind i y hy
        have hi : i < entry.numParams + entry.idx + 1 := by
          have := (List.getElem?_eq_some_iff.mp hy).1; omega
        rw [getD_reverse_of_peel (by simp; omega) hi hp]
        simpa using hd)
      (fun i hi σ hσ => by
        rw [hgetΓ hi]
        rw [hdropΓ (Nat.le_of_lt hi)] at hσ
        exact hdoms i (by omega) σ (by simpa using hσ))
      (Nat.le_of_lt hi0) hwx hopener
    rwa [hdropΓ (Nat.le_of_lt hi0)] at this
  -- the row's reading
  obtain ⟨pd, hpd, hdd⟩ := hbind _ x hx
  have hpdEq : pd = ds.getD (entry.numParams + j) default := by
    rw [List.getElem?_take_of_lt hi0] at hpd
    rw [List.getD_eq_getElem?_getD, hpd, Option.getD_some]
  subst hpdEq
  have hdd' : denote m.acval env φ (entry.numParams + j) x.fvarTypeD
      = some (ds.getD (entry.numParams + j) default) := by simpa using hdd
  have hokD : WellDenotedTy V ρ (ds.getD (entry.numParams + j) default) :=
    hdoms _ (by omega) ρ (by simpa using hsat)
  have hLG := hC.leavesGr hsat
  obtain ⟨hft, hsub, tya, htya, hrowI⟩ := hsem ⟨hwx, hbx, hLx⟩ hC.toS hdd'
  have hio := (hrowI ρ hsat hLG hokD.1).1
  obtain ⟨hokTy, hmemTy⟩ :=
    (IORel.mem_of_red hio hokD.2.ne_pt hrr (fun _ _ h => nomatch h)).of_reading htya
  obtain ⟨-, -, sa, hsa, hr⟩ := hred hft (hC.toS.of_subset hsub) htya
  rw [denote_sort] at hsa
  obtain rfl := Option.some.inj hsa
  obtain ⟨-, heq⟩ := hr ρ hsat (hLG.of_subset hsub) hokTy.1 hokTy.2.ne_pt
  rw [heq, interp_sort] at hmemTy
  rwa [ConLeche.Level.zeroWhereZero_sound hz φ hzero] at hmemTy

end ConLeche.Model.Rules
