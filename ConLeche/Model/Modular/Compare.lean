module

public import ConLeche.Model.Copies
public import ConLeche.Driver.Compare
public import ConLeche.Verify.Cached.Fill
public import ConLeche.Model.Modular.Valid
import ConLeche.Model.Modular.Main
import ConLeche.Verify.Driver.ComposeReads
import ConLeche.Verify.Driver.Reach
import ConLeche.Model.Modular.Proofs
import ConLeche.Model.OfEnvModelM

public section

/-!
# A compared challenge's records, copies of what they stand for (tasks #607, #608)

A record installing copies of another's constants at other level-parameter names (`RecCopy`),
with the same tables, and the copies of a list of records (`records_copy`): what the modular
compare worker's challenge environment is of what its records stand for
(`ConLeche/Model/Modular/CompareRun.lean`).
-/

namespace ConLeche.Model.Compare

open ConLeche ConLeche.Driver ConLeche.Verify ConLeche.Model SetTheory
open ConLeche.Cached (recordReads needsGo NeedsSt litNeeds)

/-- **A record installing copies of another's constants**, the same tables. -/
@[expose] def RecCopy (e r : Declaration) : Prop :=
  ConstsCopy (declConstants e) (declConstants r) ∧ declTables r = declTables e

theorem constsCopy_refl : ∀ l : List ConstantInfo, ConstsCopy l l
  | [] => .nil
  | _ :: l => .cons (.inl rfl) (constsCopy_refl l)

theorem RecCopy.refl (d : Declaration) : RecCopy d d := ⟨constsCopy_refl _, rfl⟩

theorem recCopy_single {c c' : ConstantInfo} {d d' : Declaration} (h : ConstCopy c c')
    (h1 : declConstants d = [c]) (h2 : declConstants d' = [c']) (ht : declTables d' = declTables d) :
    RecCopy d d' := by
  refine ⟨?_, ht⟩
  rw [h1, h2]
  exact .cons h .nil

theorem recKey_of_recCv {d : Declaration} {cv : ConstantVal} (h : recCv? d = some cv) :
    recKey d = cv.name := by
  cases d <;> simp_all [recCv?, recKey]

/-! ## The challenge's environment, a copy of what it stands for -/

theorem _root_.ConLeche.Model.ConstsCopy.append : ∀ {a a' b b' : List ConstantInfo}, ConstsCopy a a' →
    ConstsCopy b b' → ConstsCopy (a ++ b) (a' ++ b')
  | _, _, _, _, .nil, hb => hb
  | _, _, _, _, .cons hc ha, hb => .cons hc (ha.append hb)

theorem _root_.ConLeche.Model.ConstsCopy.reverse : ∀ {a a' : List ConstantInfo}, ConstsCopy a a' →
    ConstsCopy a.reverse a'.reverse
  | _, _, .nil => .nil
  | _, _, .cons hc ha => by
    simp only [List.reverse_cons]
    exact ha.reverse.append (.cons hc .nil)

theorem records_copy : ∀ (L L' : List Declaration), L.length = L'.length →
    (∀ i (h : i < L.length) (h' : i < L'.length), RecCopy L[i] L'[i]) →
    ConstsCopy (Model.Modular.recsC L) (Model.Modular.recsC L') ∧
      L'.flatMap declTables = L.flatMap declTables
  | [], [], _, _ => ⟨.nil, rfl⟩
  | d :: L, d' :: L', hl, h => by
    obtain ⟨h1, h2⟩ := records_copy L L' (by simpa using hl)
      (fun i hi hi' => h (i + 1) (by simp; omega) (by simp; omega))
    obtain ⟨h3, h4⟩ := h 0 (by simp) (by simp)
    simp only [Model.Modular.recsC, List.flatMap_cons] at h1 h2 ⊢
    exact ⟨h3.append h1, by simp only [List.getElem_cons_zero] at h4; rw [h4, h2]⟩
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

end ConLeche.Model.Compare
