module

public import ConLeche.Frontend.Olean.Present
public import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.View
import ConLeche.Verify.Frontend.Olean.Equiv

/-!
# A constant read with a part's memo is the specification's

`entryWith_spec`, `stmtWith_spec` (`ConLeche/Frontend/Olean/Present.lean`): a constant read
with a part's memo, or its statement and kind, is what the memo-less read gives, and the
memo stays good; `entryWith_of_view`, `stmtWith_of_view`: at a position of a parsed view,
the full parse's constant there (`readEntry_of_view`), the specification's
(`parseView_eq_spec`).
-/

public section

/-! ## A copy read is the specification's -/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- **A constant read with a part's memo is the specification's**, and the memo stays
good. -/
theorem entryWith_spec {r : Region} {st : SM} (hG : st.Good r) {c : Nat}
    {p : SM × CEntryF Name Expr} (h : entryWith r st c = some p) :
    p.1.Good r ∧ entryAt r c = some p.2 := by
  simp only [entryWith] at h
  obtain ⟨sk, hsk, h⟩ := bind_some_left h
  have hG' := memoRoots_good hG sk
  rw [memoName_eq hG', memoExpr_eq hG'] at h
  obtain ⟨e, he, h⟩ := bind_some_left h
  cases h
  refine ⟨hG', ?_⟩
  simp only [entryAt, hsk, Option.bind_eq_bind, Option.bind_some, sparseEntry_eq]
  exact he

/-- **A statement and kind read with a part's memo are the specification's**: the full
constant's statement and kind constructor, where it reads; and the memo stays good. -/
theorem stmtWith_spec {r : Region} {st : SM} (hG : st.Good r) {c : Nat} {st' : SM}
    {cv : ConstantVal} {k : CKindF Name Unit} (h : stmtWith r st c = some (st', cv, k))
    {e : CEntryF Name Expr} (he : entryAt r c = some e) :
    st'.Good r ∧ cv = e.stmt ∧ k.tag = e.kind.tag := by
  simp only [stmtWith] at h
  obtain ⟨sk, hsk, h⟩ := bind_some_left h
  have hG' : (memoAdd r kExpr ((sk.name :: sk.levelParams).foldl (memoAdd r kName) st)
      sk.type).Good r :=
    memoAdd_good isKind_expr (foldl_memoAdd_good isKind_name _ _ hG) _
  rw [memoName_eq hG', memoExpr_eq hG'] at h
  obtain ⟨n, hn, h⟩ := bind_some_left h
  obtain ⟨lps, hl, h⟩ := bind_some_left h
  obtain ⟨ty, ht, h⟩ := bind_some_left h
  obtain ⟨k', hk, h⟩ := bind_some_left h
  cases h
  simp only [entryAt, hsk, Option.bind_eq_bind, Option.bind_some, sparseEntry_eq] at he
  obtain ⟨hn', hl', ht', htag, -⟩ := CEntryF.mapM_parts he
  refine ⟨hG', ?_, ?_⟩
  · rw [hn] at hn'; rw [hl] at hl'; rw [ht] at ht'
    cases hn'; cases hl'; cases ht'
    rfl
  · rw [← htag]; exact (CKindF.mapM_tag hk).1.symm

/-- **A constant read at a position of a parsed view, with the part's memo, is the full
parse's constant there** (`readEntry_of_view`), the specification's (`parseView_eq_spec`). -/
theorem entryWith_of_view {f : ModFiles} {level : OLeanLevel} {d : ModDecoded}
    {ps : NamePositions} {i : Nat} {q : NamePosition} {r : Region} {a : UInt64} {st : SM}
    {p : SM × CEntryF Name Expr} (hv : parseView f level = some d)
    (hp : readNamePositions f level = some ps) (hq : ps.consts[i]? = some q)
    (hr : f.viewRegion level = some (r, a)) (hG : st.Good r) (h : entryWith r st q.loc = some p) :
    d.constants[i]? = some p.2 ∧ p.1.Good r := by
  obtain ⟨hG', he⟩ := entryWith_spec hG h
  have hre := readEntry_of_view hv hp hq
  simp only [readEntry, hr, bind, Option.bind] at hre
  exact ⟨hre ▸ he, hG'⟩

/-- **A statement and kind read at a position of a parsed view, with the part's memo, are
the full parse's constant's there.** -/
theorem stmtWith_of_view {f : ModFiles} {level : OLeanLevel} {d : ModDecoded}
    {ps : NamePositions} {i : Nat} {q : NamePosition} {r : Region} {a : UInt64} {st st' : SM}
    {cv : ConstantVal} {k : CKindF Name Unit} (hv : parseView f level = some d)
    (hp : readNamePositions f level = some ps) (hq : ps.consts[i]? = some q)
    (hr : f.viewRegion level = some (r, a)) (hG : st.Good r)
    (h : stmtWith r st q.loc = some (st', cv, k)) :
    ∃ e, d.constants[i]? = some e ∧ cv = e.stmt ∧ k.tag = e.kind.tag ∧ st'.Good r := by
  have hre := readEntry_of_view hv hp hq
  simp only [readEntry, hr, bind, Option.bind] at hre
  obtain ⟨e, he⟩ : ∃ e, d.constants[i]? = some e := by
    obtain ⟨ps', hps', -, hnames, -⟩ := readNamePositions_of_view hv
    rw [hp] at hps'; cases hps'
    have hi : i < ps.consts.size := (Array.getElem?_eq_some_iff.1 hq).1
    have hlen : ps.consts.size = d.constants.size := by simpa using congrArg List.length hnames
    exact ⟨d.constants[i]'(hlen ▸ hi), by simp⟩
  obtain ⟨g1, g2, g3⟩ := stmtWith_spec hG h (hre.trans he)
  exact ⟨e, he, g2, g3, g1⟩

end ConLeche.Frontend.Olean
