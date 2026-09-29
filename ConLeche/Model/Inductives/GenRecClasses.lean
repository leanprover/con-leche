module

public import ConLeche.Verify.Inductives.GenRecRun
public import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Verify.Inductives.NestScope

public section

/-!
# The generated recursor stage: the classes' constructors and outside data

The facts of the generated stage (`GenRecRun`) about the CLASSES its
stored recursors eliminate, for the stage's assembly (`genRecStage`,
`GenRecAssembly.lean`):

* `genRecClassAt` — the stored family's `j`-th major is a class the stage
  checked as a major (`ClassMajorRun`), with its table entries: the
  recursor's class (the pre-pass's `recCls`) is in range
  (`classRead_recCls_lt`), and `out[j]`'s major is `classesNfs`'s entry
  there (`classRecsRulesOk_run`, `classesNfs_run`, `classMajors_run`);
* `genRecCtor_find` / `genRecCtor_in` / `genRecCtor_seam` — the skeleton's
  `ctorsIn` and `hctor`: every constructor a stored recursor carries is
  stored, at its class's parameter count (a member's by the constructors'
  core record, an outside class's by the carrier's coverage,
  `tgtOutCls_ofR`);
* `genOutCls` — the outside classes' recorded blocks, canonically selected
  (`tgtOutCls_selR`), the data both B-lanes take.
-/

namespace ConLeche

/-! ## The pre-pass's classes are in range

The pre-pass reads every recursor's class as a motive ORDINAL
(`classOfMotiveVar`: an index into the motives' positions), so it is
below the number of motives, which is the number of classes.  Nothing
else is read from how the pre-pass ran. -/

/-- Filtering the positions of a list by a predicate on the entry counts
the entries. -/
theorem range_filter_getElem?_length {α : Type} (q : Option α → Bool) :
    ∀ l : List α, ((List.range l.length).filter fun s => q l[s]?).length
      = (l.filter fun a => q (some a)).length
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons]
    have ih := range_filter_getElem?_length q l
    have hmap : ((List.range l.length).map Nat.succ).filter (fun s => q (a :: l)[s]?)
        = ((List.range l.length).filter fun s => q l[s]?).map Nat.succ := by
      rw [List.filter_map]; rfl
    rw [List.filter_cons]
    by_cases ha : q (some a) = true
    · simp only [List.getElem?_cons_zero, ha, if_true, List.length_cons, hmap,
        List.length_map, ih]
    · simp only [List.getElem?_cons_zero, ha, Bool.false_eq_true, if_false, hmap,
        List.length_map, ih]

/-- The motives' positions are as many as the classes. -/
theorem classRead_motPos_length (slots : List ClassSlot) :
    ((List.range slots.length).filter fun s =>
        match slots[s]? with | some (.motive _) => true | _ => false).length
      = (ClassRead.classes ⟨slots, []⟩).length := by
  refine (range_filter_getElem?_length
    (fun o : Option ClassSlot => match o with | some (.motive _) => true | _ => false)
    slots).trans ?_
  unfold ClassRead.classes
  simp only

  induction slots with
  | nil => rfl
  | cons a l ih =>
    cases a <;> simp [List.filter_cons, List.filterMap_cons, ih]

/-- **Every recursor's class is a class**: the pre-pass's `recCls` entries
are below the number of classes it read. -/
theorem classRead_recCls_lt {nP : Nat} {nPc : Name → Nat} {recs : List RecShape}
    {rd : ClassRead} (h : classRead nP nPc recs = some rd) :
    ∀ c ∈ rd.recCls, c < rd.classes.length := by
  unfold classRead at h
  obtain ⟨rc0, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨fvs0, body⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨slots, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨recCls, hrc, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  intro c hc
  obtain ⟨rc, -, hf⟩ := option_mapM_mem hrc c hc
  obtain ⟨⟨fvs, concl⟩, -, hf⟩ := Option.bind_eq_some_iff.mp hf
  simp only at hf
  split at hf
  · next p _ _ =>
    unfold classOfMotiveVar at hf
    split at hf
    · obtain ⟨hlt, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      exact Nat.lt_of_lt_of_eq hlt (classRead_motPos_length slots)
    · exact nomatch hf
  · exact nomatch hf

/-! ## The stored family's majors are the checked classes -/

variable {mode : CheckMode}

/-- **The `j`-th stored recursor's major is a checked class**: `out[j]`'s
major is the class `rd.recCls[j]` with its table entries
(`classesNfs`), the class checked as a major (`ClassMajorRun`) at the
class key. -/
theorem genRecClassAt {F : Nat} {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockShape}
    {nb : Bool} {pos : NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : GenRecRun mode F fe₁ env₁ fe p nb pos cvTas block ctorsAs out)
    {j : Nat} {t : ConstantVal × TargetMajor × List Expr} (ho : out[j]? = some t) :
    ∃ key M₀ nfs, t.2.1 = { M₀ with nfs := nfs } ∧
      Nonempty (ClassMajorRun mode F fe p ctorsAs R.pfvs key M₀) := by
  obtain ⟨hlenO, hallO⟩ := classRecsRulesOk_run R.hrules
  have hj : j < out.length := (List.getElem?_eq_some_iff.mp ho).1
  obtain ⟨cvG, hcvG⟩ : ∃ cvG, R.cvGs[j]? = some cvG :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨c, hc⟩ : ∃ c, R.rd.recCls[j]? = some c :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨rhss, ho', -⟩ := hallO j cvG c hcvG hc
  obtain rfl := Option.some.inj (ho.symm.trans ho')
  have hcl : c < R.rd.classes.length :=
    classRead_recCls_lt R.hrd c (List.mem_of_getElem? hc)
  obtain ⟨hlen₀, hall₀⟩ := classMajors_run R.hMs₀
  obtain ⟨hlenN, hallN⟩ := classesNfs_run R.hMs
  obtain ⟨key, hkey⟩ : ∃ key, R.rd.classes[c]? = some key :=
    ⟨_, List.getElem?_eq_getElem hcl⟩
  obtain ⟨M₀, hM₀, ⟨Rc⟩⟩ := hall₀ c key hkey
  obtain ⟨nfs, hMs, -⟩ := hallN c M₀ hM₀
  refine ⟨key, M₀, nfs, ?_, ⟨Rc⟩⟩
  change (R.Ms.getD c default) = _
  rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]

end ConLeche
