module

public import ConLeche.Model.Inductives.GenRecAssembly
public import ConLeche.Model.Inductives.TargetNodeRead
public import ConLeche.Verify.Inductives.GenK53Rename
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Semantics.Tower.TowerKit

public section

/-!
# The generated calls' kit (lane GENREC-B2)

* `openPis_stripPis_locOpen` — an `ih`'s telescope opened at variables
  (`ClassGen.ihParts`) is its `stripPis` split, the leaf opened at the
  canonical openers (`locOpen`) up to annotations, and its domains' reading
  (`readOpenedDoms`) is the telescope's (`teleDoms`) whenever that reads;
* `genFap_read` — the applied field of a call, read at the call's
  valuation, is the field value applied to the telescope's values;
* `genRecIdx_spec` — the recursor a generated rule calls at class `t`
  (`genRecIdx`) is a recursor at class `t`, below the family's length.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V]

private theorem gc_instantiateList_congr : ∀ (vs vs' : List Expr), vs.length = vs'.length →
    (∀ (j : Nat) (h : j < vs.length) (h' : j < vs'.length), Expr.ErasedEq vs[j] vs'[j]) →
    ∀ (e : Expr) (d : Nat), Expr.ErasedEq (e.instantiateList vs d) (e.instantiateList vs' d)
  | [], [], _, _, e, d => by
    simp only [Expr.instantiateList_nil]; exact Expr.ErasedEq.rfl _
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | v :: vs, v' :: vs', hl, h, e, d => by
    rw [Expr.instantiateList_cons, Expr.instantiateList_cons]
    exact Expr.ErasedEq.instantiate1
      (gc_instantiateList_congr vs vs' (by simpa using hl)
        (fun j hj hj' => h (j + 1) (by simpa using hj) (by simpa using hj')) e (d + 1))
      (h 0 (by simp) (by simp))

private theorem gc_locList_erased {D : Nat} {os : List Expr} (hos : LocList D os.length os) :
    ∀ (e : Expr) (d : Nat),
      Expr.ErasedEq (e.instantiateList os d) (e.instantiateList (locOpen D os.length) d) := by
  refine gc_instantiateList_congr _ _ (by simp [locOpen]) (fun j hj hj' => ?_)
  obtain ⟨ty, hty⟩ := hos.2 j hj
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hty
  rw [hty]
  simp [locOpen, Expr.ErasedEq]

private theorem gc_openPis_gen {D : Nat} :
    ∀ (n : Nat) (e : Expr) (os : List Expr) {xsO : List Expr} {leafO : Expr},
      LocList D os.length os →
      openPisAtFvars n (e.instantiateList os 0) (D + os.length) = some (xsO, leafO) →
      ∃ (tele : List (Expr × ConLeche.BinderMeta)) (leaf : Expr),
        e.stripPis n = some (tele, leaf) ∧ xsO.length = n ∧
        (∀ l, l < n → ∃ ty, xsO[l]? = some (.fvar (D + os.length + l) ty)) ∧
        Expr.ErasedEq leafO (leaf.instantiateList (locOpen D (os.length + n)) 0) ∧
        ∀ (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (ψ : Name → Nat)
          (doms : List AnnotTerm),
          teleDoms acval env ψ D os (tele.map (·.1)) = some doms →
          readOpenedDoms acval env ψ (D + os.length) xsO = doms
  | 0, e, os, xsO, leafO, hos, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨[], e, rfl, rfl, fun l hl => absurd hl (Nat.not_lt_zero _), ?_, ?_⟩
    · rw [Nat.add_zero]; exact gc_locList_erased hos e 0
    · intro acval env ψ doms hd
      simp only [List.map_nil, teleDoms, Option.some.injEq] at hd
      subst hd; rfl
  | n + 1, e, os, xsO, leafO, hos, h => by
    cases e with
    | forallE ty b m =>
      rw [Expr.instantiateList] at h
      simp only [openPisAtFvars] at h
      split at h
      · rename_i xs' lf hop
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [← Expr.instantiateList_cons] at hop
        have hos' : LocList D (Expr.fvar (D + os.length) (ty.instantiateList os 0) :: os).length
            (Expr.fvar (D + os.length) (ty.instantiateList os 0) :: os) := by
          refine ⟨rfl, fun j hj => ?_⟩
          cases j with
          | zero => exact ⟨ty.instantiateList os 0, by simp⟩
          | succ j =>
            obtain ⟨ty', hty'⟩ := hos.2 j (by simp at hj; omega)
            refine ⟨ty', ?_⟩
            rw [List.getElem?_cons_succ, hty']
            simp only [List.length_cons]
            congr 2
            omega
        rw [show D + os.length + 1 = D + (Expr.fvar (D + os.length) (ty.instantiateList os 0)
          :: os).length by simp; omega] at hop
        obtain ⟨tele, leaf, hst, hl, hidx, her, hrd⟩ := gc_openPis_gen n b _ hos' hop
        refine ⟨(ty, m) :: tele, leaf, by simp [Expr.stripPis, hst], by simp [hl], ?_, ?_, ?_⟩
        · intro l hl'
          cases l with
          | zero => exact ⟨ty.instantiateList os 0, by simp⟩
          | succ l =>
            obtain ⟨ty', hty'⟩ := hidx l (by omega)
            refine ⟨ty', ?_⟩
            rw [List.getElem?_cons_succ, hty']
            simp only [List.length_cons]
            congr 2
            omega
        · simp only [List.length_cons] at her
          rw [show os.length + (n + 1) = os.length + 1 + n by omega]
          exact her
        · intro acval env ψ doms hd
          simp only [List.map_cons, teleDoms] at hd
          obtain ⟨a, ha, hd⟩ := Option.bind_eq_some_iff.mp hd
          obtain ⟨r, hr, hd⟩ := Option.bind_eq_some_iff.mp hd
          simp only [Option.pure_def, Option.some.injEq] at hd
          subst hd
          have := hrd acval env ψ r hr
          simp only [List.length_cons] at this
          show (denoteMeta acval env ψ (D + os.length) (ty.instantiateList os 0)).getD default
            :: readOpenedDoms acval env ψ (D + os.length + 1) xs' = _
          rw [ha, Option.getD_some, show D + os.length + 1 = D + (os.length + 1) by omega, this]
      · exact nomatch h
    | bvar j =>
      exfalso
      rw [Expr.instantiateList] at h
      split at h
      · rename_i hj0; exact absurd hj0 (Nat.not_lt_zero _)
      · split at h
        · rename_i hj
          obtain ⟨ty', hty'⟩ := hos.2 (j - 0) hj
          rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hty'
          rw [hty', Expr.instantiateList] at h
          simp [openPisAtFvars] at h
        · simp [openPisAtFvars] at h
    | _ => rw [Expr.instantiateList] at h; simp [openPisAtFvars] at h

/-- **An `ih`'s telescope, opened**: see the module docstring. -/
theorem openPis_stripPis_locOpen {n D : Nat} {w : Expr} {xsO : List Expr} {leafO : Expr}
    (h : openPisAtFvars n w D = some (xsO, leafO)) :
    ∃ (tele : List (Expr × ConLeche.BinderMeta)) (leaf : Expr),
      w.stripPis n = some (tele, leaf) ∧ xsO.length = n ∧
      (∀ l, l < n → ∃ ty, xsO[l]? = some (.fvar (D + l) ty)) ∧
      Expr.ErasedEq leafO (leaf.instantiateList (locOpen D n) 0) ∧
      ∀ (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (ψ : Name → Nat)
        (doms : List AnnotTerm),
        teleDoms acval env ψ D [] (tele.map (·.1)) = some doms →
        readOpenedDoms acval env ψ D xsO = doms := by
  rw [← Expr.instantiateList_nil w 0, show D = D + ([] : List Expr).length from rfl] at h
  obtain ⟨tele, leaf, hst, hl, hidx, her, hrd⟩ := gc_openPis_gen n w [] (LocList.nil D) h
  simp only [List.length_nil, Nat.add_zero, Nat.zero_add] at hidx her hrd
  exact ⟨tele, leaf, hst, hl, hidx, her, hrd⟩

/-- **A call's applied field, read**: the field `fvar (rP + i)` applied
to the telescope's openers `fvar (rP + nF + l)`, read at the call's
valuation, is the field's value applied to the telescope's values. -/
theorem genFap_read {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {ψ : Name → Nat}
    {rP nF m i : Nat} {f : Expr} {xsO : List Expr} (hi : i < nF)
    (hf : ∃ ty, f = .fvar (rP + i) ty)
    (hxsO : ∀ l, l < m → ∃ ty, xsO[l]? = some (.fvar (rP + nF + l) ty)) (hm : xsO.length = m)
    {xs fs bs : List V} (hxl : xs.length = rP) (hfl : fs.length = nF) (hbl : bs.length = m)
    (ρ : Nat → V) :
    interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta acval env ψ (rP + nF + m) (Expr.mkAppN f xsO)).getD default)
      = bs.foldl app (fs.getD i pt) := by
  obtain ⟨ty, rfl⟩ := hf
  have hvl : (xs ++ fs ++ bs).length = rP + nF + m := by simp [hxl, hfl, hbl]; omega
  obtain ⟨ra, hra, hint⟩ := interp_denoteMeta_fvarSpine (ρ := ρ) hvl xsO _ _
    (denoteMeta_fvar acval (env := env) (φ := ψ) (rP + nF + m) (rP + i) ty) (by
      intro a ha
      obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty', h'⟩ := hxsO l (by omega)
      rw [List.getElem?_eq_getElem hl, Option.some.injEq] at h'
      exact ⟨_, _, h', by omega⟩)
  rw [← consList_append, hra, Option.getD_some, hint]
  congr 1
  · rw [interp_bvar, consList_getD_of_lt _ _ _ (by rw [hvl]; omega), hvl,
      show rP + nF + m - 1 - (rP + nF + m - 1 - (rP + i)) = rP + i by omega,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_right (by omega), hxl, Nat.add_sub_cancel_left,
      List.getElem?_append_left (by omega)]
  · apply List.ext_getElem (by simp [hm, hbl])
    intro l h1 h2
    simp only [List.getElem_map]
    obtain ⟨ty', h'⟩ := hxsO l (by simp at h1; omega)
    rw [List.getElem?_eq_getElem (by simpa using h1), Option.some.injEq] at h'
    rw [h']
    simp only [fvIdx]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hxl, hfl]),
      List.getElem?_eq_getElem (by simp [hxl, hfl]; omega)]
    simp [hxl, hfl]

/-- **The generated rules' callee at class `t`** (`genRecIdx`, the
kernel's `classRecOf` as a position): a recursor at class `t`, below the
generated family's length. -/
theorem genRecIdx_spec {rd : ClassRead} {cvGs : List ConstantVal} {t : Nat} {n : Name}
    (h : ConLeche.classRecOf rd.recCls cvGs t = some n) (hle : cvGs.length ≤ rd.recCls.length) :
    rd.recCls[genRecIdx rd t]? = some t ∧ genRecIdx rd t < cvGs.length := by
  unfold ConLeche.classRecOf at h
  obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.mp h
  have hrl := List.mem_range.mp (List.mem_of_find?_eq_some hr)
  have hrt := List.find?_some hr
  have hfind : (List.range rd.recCls.length).find? (fun r => rd.recCls.getD r 0 == t) = some r := by
    rw [show rd.recCls.length = cvGs.length + (rd.recCls.length - cvGs.length) by omega,
      List.range_add, List.find?_append, hr]
    rfl
  have hg : genRecIdx rd t = r := by unfold genRecIdx; rw [hfind]; rfl
  rw [hg]
  simp only [beq_iff_eq] at hrt
  refine ⟨?_, hrl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at hrt
  rw [List.getElem?_eq_getElem (by omega)]
  simpa using hrt

end ConLeche.Model
