module

public import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Verify.Inductives.NestScope
public import ConLeche.Model.Inductives.NestedRecRest
public import ConLeche.Model.Inductives.BlockDeclRun
public import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.TargetClass

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
    · simp only [List.getElem?_cons_zero, ha, ite_true, List.length_cons, hmap,
        List.length_map, ih]
    · simp only [List.getElem?_cons_zero, ha, Bool.false_eq_true, ite_false, hmap,
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
    cases a <;> simp [ih]

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
    {nb : Bool} {pos : NestState} {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : GenRecRun mode F fe₁ env₁ fe p nb pos block out)
    {j : Nat} {t : ConstantVal × TargetMajor × List Expr} (ho : out[j]? = some t) :
    ∃ key M₀ nfs, t.2.1 = { M₀ with nfs := nfs } ∧
      Nonempty (ClassMajorRun mode F fe p R.ctx.params key M₀) := by
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
  obtain ⟨hlen₀, hall₀⟩ := R.majors
  obtain ⟨hlenN, hallN⟩ := classesNfs_run R.hMs
  obtain ⟨key, hkey⟩ : ∃ key, R.keys[c]? = some key :=
    ⟨_, List.getElem?_eq_getElem (by rw [R.keys_length]; exact hcl)⟩
  obtain ⟨M₀, hM₀, ⟨Rc⟩⟩ := hall₀ c key hkey
  obtain ⟨nfs, hMs, -⟩ := hallN c M₀ hM₀
  refine ⟨key, M₀, nfs, ?_, ⟨Rc⟩⟩
  change (R.Ms.getD c default) = _
  rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify

open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockShape BlockShape
  TargetMajor FEnv GenRecRun ClassMajorRun NestState)

universe w

variable {V : Type w} [SetTheory V]

section Ctors

variable {F : Nat} {fe₁ : FEnv} {env₁ : Env} {envC : Env} {pp : BlockShape} {nb : Bool}
  {pos : NestState} {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V envC} {dR : BlockData V} {isRec : Bool}
  {A : Nat → (Name → Nat) → Term}

/-- The `j`-th stored record, as `out`'s `j`-th entry. -/
theorem tgtRs_getElem? {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) :
    ∃ t, out[j]? = some t ∧ r = (t.1, t.2.2, t.2.1.nIdx, t.2.1.ctors) ∧
      ConLeche.tgtMajorsOf out j = t.2.1 := by
  simp only [tgtRs, List.getElem?_map] at hr
  cases ho : out[j]? with
  | none => rw [ho] at hr; exact nomatch hr
  | some t =>
    rw [ho] at hr
    refine ⟨t, rfl, (Option.some.inj hr).symm, ?_⟩
    simp [ConLeche.tgtMajorsOf, List.getD_eq_getElem?_getD, ho]

/-- **Every constructor a generated recursor carries is stored, at its
class's parameter count** — a member class's by the constructors' core
record, an outside class's by the carrier's coverage (`tgtOutCls_ofR` at
the class's run as a major). -/
theorem genRecCtor_find
    (R : GenRecRun .verified F fe₁ env₁ (ConLeche.mkFEnv envC) pp nb pos block out)
    (hN : BlockNamesOk (V := V) dR pp.formers)
    (hcore : BlockCtorsCore mpC.base2 dR pp.lps pp.formers pp isRec A dR.k)
    (hmemberCtors : ∀ c, c < pp.memberCtors.length → pp.memberCtors[c]? = some (dR.ctorsM c))
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
      (ppsOf : Nat → (Name → Nat) → List Term),
      dR = blockDataOf V pp pk uOfD ppsOf)
    (hcov : LfpCover mpC []) (hrd : ∀ F, FamilyRead mpC F) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat), r.2.2.2[i]? = some ctor →
        envC.find? ctor.1.name
          = some (.ctorInfo ctor.1 (ConLeche.tgtMajorsOf out j).nPc ctor.2) := by
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  intro j r hr i ctor hctor
  obtain ⟨t, ho, rfl, hMj⟩ := tgtRs_getElem? hr
  obtain ⟨key, M₀, nfs, hM, ⟨Rc⟩⟩ := ConLeche.genRecClassAt R ho
  rw [hMj, hM]
  simp only at hctor ⊢
  rw [hM] at hctor
  simp only at hctor
  cases hm : M₀.member with
  | some t' =>
    obtain ⟨hctors, hnPc⟩ := Rc.major.member_facts hm
    have hcl : t' < pp.memberCtors.length := (List.getElem?_eq_some_iff.mp hctors).1
    have heq : M₀.ctors = (blockDataOf V pp pk uOfD ppsOf).ctorsM t' :=
      Option.some.inj (hctors.symm.trans (hmemberCtors _ hcl))
    rw [heq] at hctor
    have hck : t' < (blockDataOf V pp pk uOfD ppsOf).k := by
      rw [← hN.2.2]; exact hN.2.1 _ i ctor hctor
    obtain ⟨hfind, -, -⟩ := hcore.2.2 _ hck i ctor hctor
    rw [hnPc]
    exact hfind
  | none =>
    obtain ⟨D, mm, cvI, hD⟩ := tgtOutCls_ofR hcov hrd Rc.major hm
    have hi : i < M₀.ctors.length := (List.getElem?_eq_some_iff.mp hctor).1
    have hc := hD.hctor i hi
    have hctor' : M₀.ctors[i] = ctor := (List.getElem?_eq_some_iff.mp hctor).2
    rw [hctor'] at hc
    have hname := ConLeche.Env.find?_name hc
    simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hname
    rw [hname]
    exact hc

/-- **`ctorsIn` at the generated stage**: every constructor a stored
recursor carries is stored. -/
theorem genRecCtor_in
    (R : GenRecRun .verified F fe₁ env₁ (ConLeche.mkFEnv envC) pp nb pos block out)
    (hN : BlockNamesOk (V := V) dR pp.formers)
    (hcore : BlockCtorsCore mpC.base2 dR pp.lps pp.formers pp isRec A dR.k)
    (hmemberCtors : ∀ c, c < pp.memberCtors.length → pp.memberCtors[c]? = some (dR.ctorsM c))
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
      (ppsOf : Nat → (Name → Nat) → List Term),
      dR = blockDataOf V pp pk uOfD ppsOf)
    (hcov : LfpCover mpC []) (hrd : ∀ F, FamilyRead mpC F) :
    ∀ r ∈ tgtRs out, ∀ ctor ∈ r.2.2.2,
      ∃ cvj cnP cnF, envC.find? ctor.1.name = some (.ctorInfo cvj cnP cnF) := by
  intro r hr ctor hctor
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hctor
  exact ⟨_, _, _, genRecCtor_find R hN hcore hmemberCtors hdR hcov hrd j r hj i ctor hi⟩

/-- **`hctor` at the generated stage**: the carried constructors, stored
at the class's parameter count, their types bound and read. -/
theorem genRecCtor_seam
    (R : GenRecRun .verified F fe₁ env₁ (ConLeche.mkFEnv envC) pp nb pos block out)
    (hN : BlockNamesOk (V := V) dR pp.formers)
    (hcore : BlockCtorsCore mpC.base2 dR pp.lps pp.formers pp isRec A dR.k)
    (hmemberCtors : ∀ c, c < pp.memberCtors.length → pp.memberCtors[c]? = some (dR.ctorsM c))
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
      (ppsOf : Nat → (Name → Nat) → List Term),
      dR = blockDataOf V pp pk uOfD ppsOf)
    (hcov : LfpCover mpC []) (hrd : ∀ F, FamilyRead mpC F) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat), r.2.2.2[i]? = some ctor →
        envC.find? ctor.1.name = some (.ctorInfo ctor.1 (ConLeche.tgtMajorsOf out j).nPc ctor.2) ∧
        ConstsBound envC ctor.1.type ∧
        ∀ ψ : Name → Nat,
          denote mpC.base2.acval envC ψ 0 ctor.1.type
            = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) :=
  tgtRecCtor_seam_of_find (genRecCtor_find R hN hcore hmemberCtors hdR hcov hrd)

end Ctors

/-! ## The outside classes' data -/

/-- An outside class's record reads only the major's inductive, its
constructors and its parameter count: it survives the table entries'
update. -/
theorem TgtOutCls.withNfs {env : Env} {mp : EnvModelM V env} {M : TargetMajor}
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal} (h : TgtOutCls mp M D mm cvI)
    (nfs : List ConLeche.NestCtorNf) : TgtOutCls mp { M with nfs := nfs } D mm cvI :=
  ⟨h.hD, h.hmm, h.hmem, h.hfind, h.hread, h.hnd, h.hnN, h.hkN, h.hlen, h.hctor⟩

/-- **The outside classes' recorded blocks, canonically selected**: at
every stored recursor whose class is outside, the class is member `mc c`
of the SELECTED recorded block holding its inductive (`lfpSel`), stored
as `cvc c` (`tgtOutCls_selR` at the class's run as a major). -/
theorem genOutCls {F : Nat} {fe₁ : FEnv} {env₁ : Env} {envC : Env} {p : BlockShape} {nb : Bool}
    {pos : NestState} {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
    {mpC : EnvModelM V envC}
    (R : GenRecRun .verified F fe₁ env₁ (ConLeche.mkFEnv envC) p nb pos block out)
    (hcov : LfpCover mpC []) (hrd : ∀ F, FamilyRead mpC F) (D0 : LfpDatum V) :
    ∃ (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal),
      (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
        TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c)) ∧
      (∀ c, Dc c = lfpSel mpC D0 (tgtMajor out c).ind) := by
  have hcls0 : ∀ c, ∃ t : Nat × ConstantVal,
      c < (tgtRs out).length → (tgtMajor out c).member = none →
        TgtOutCls mpC (tgtMajor out c) (lfpSel mpC D0 (tgtMajor out c).ind) t.1 t.2 := by
    intro c
    by_cases hc : c < (tgtRs out).length
    · by_cases hm : (tgtMajor out c).member = none
      · obtain ⟨r, hr⟩ : ∃ r, (tgtRs out)[c]? = some r := ⟨_, List.getElem?_eq_getElem hc⟩
        obtain ⟨t, ho, -, -⟩ := tgtRs_getElem? hr
        obtain ⟨key, M₀, nfs, hM, ⟨Rc⟩⟩ := ConLeche.genRecClassAt R ho
        have hMc : tgtMajor out c = { M₀ with nfs := nfs } := by
          rw [← hM]; simp [tgtMajor, List.getD_eq_getElem?_getD, ho]
        rw [hMc] at hm ⊢
        obtain ⟨mm, cvI, hD⟩ := tgtOutCls_selR hcov hrd D0 Rc.major hm
        exact ⟨(mm, cvI), fun _ _ => hD.withNfs nfs⟩
      · exact ⟨(0, default), fun _ h' => absurd h' hm⟩
    · exact ⟨(0, default), fun h' => absurd h' hc⟩
  obtain ⟨tc, hcls⟩ := Classical.axiomOfChoice hcls0
  exact ⟨fun c => lfpSel mpC D0 (tgtMajor out c).ind, fun c => (tc c).1, fun c => (tc c).2,
    fun c hc hm => hcls c hc hm, fun _ => rfl⟩

end ConLeche.Model
