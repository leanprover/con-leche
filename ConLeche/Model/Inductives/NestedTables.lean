module

public import ConLeche.Model.Inductives.BlockStageTables
public import ConLeche.Model.Inductives.MutualTables
public import ConLeche.Verify.Inductives.NestedTablesInv

public section

/-!
# The nested install's table stage, at the model (task #315, M7-2)

`nestedTables` (`ConLeche/Kernel/Inductives/NestedInstall.lean`) is the
nested install's last stage: it walks the restored members and conses
the projection table of each structure-like one.  This file carries the
two model-side facts across it.

* **The crossing** (`nestedTables_cross`): the stage creates no
  projection slot outside the block's own members and moves no stored
  name — `TableCross` (`MutualTables.lean`), the mutual twin's
  relation, which is generic in the two environments.
* **The stage** (`stageNestedTables`): a model of the environment the
  recursors left crosses to `envOut`, with a carrier that values every
  OLD constant as before (`AcvalAgrees`).

Both are the mutual route's proofs, taken at the nested route's
inversions.  The stage in particular is NOT a second copy: the fold's
real content — the transport of a member's table data across the OTHER
members' conses, and the carrier bookkeeping — is `stageTablesGo`
(`BlockStageTables.lean`), which this file instantiates at the nested
run and at `NestedMemberTableOk`, the per-element clause below.

`NestedMemberTableOk` is where the two routes differ.  The mutual one
(`MemberTableOk`) reads the table's data OFF THE BLOCK — `b.lps`,
`b.nP`, the constructor at `b.ownCtors mIdx`, the field sorts at
`sortss` — because `mutualMemberTable` recomputes them there.  The
nested stage instead takes the scratch block's RECORDED table and
recomputes only its bodies, so the clause is stated at the table's own
fields, and the three data the P step fixes — that the recorded
constructor name is the restored constructor's, that the offset is `1`
and that the guards are the field sorts' `structProjGuards` — are
conjuncts of the clause rather than facts of a block record.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal ProjTable projTableName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The crossing -/

/-- **The tables' stage crosses**: each member conses nothing or its
own table, whose structure is that member (`nestedMemberTable_inv`). -/
theorem nestedTables_cross {Ts : List Name} :
    ∀ (l : List (Name × Option ProjTable × List (ConstantVal × Nat × Nat))) {env env' : Env},
      ConLeche.nestedTables (m := ConLeche.CheckM) l env = .ok env' →
      (∀ e ∈ l, e.1 ∈ Ts) → TableCross Ts env env' := by
  intro l
  induction l with
  | nil =>
    intro env env' h _
    obtain rfl := ConLeche.nestedTables_nil_inv h
    exact TableCross.rfl' Ts _
  | cons e rest ih =>
    intro env env' h hTs
    obtain ⟨T, tbl?, cs⟩ := e
    obtain ⟨envI, hI, hrest⟩ := ConLeche.nestedTables_inv h
    have hrestTs : ∀ q ∈ rest, q.1 ∈ Ts := fun q hq => hTs q (List.mem_cons_of_mem _ hq)
    rcases ConLeche.nestedMemberTable_inv hI with rfl | ⟨tbl, cvCa, nP, nF, -, -, htbl⟩
    · exact ih hrest hrestTs
    · obtain ⟨bodies, -, -, -, hfreshTbl, rfl⟩ := ConLeche.checkStructProjTable_inv htbl
      refine TableCross.trans (TableCross.of_table (Ts := Ts) ?_ ?_) (ih hrest hrestTs)
      · exact hTs (T, tbl?, cs) List.mem_cons_self
      · exact hfreshTbl

/-! ## A restored member's table data -/

/-- **A restored member's table data, when the kernel conses its
table**: at a structure-like member — a RECORDED table and exactly one
restored constructor — the flat bundle at that constructor, tagged `0`
(its member-local position), at the table's own level parameters and
result sort; at any other member nothing (`nestedMemberTable` conses
nothing there, `nestedMemberTable_inv`).

The three equations are what the stage's own call fixes and the P step
(`BlockTableStep`) asks for: the table's recorded constructor name is
the restored constructor's, its offset is `1`, and its guards are the
field sorts' `structProjGuards` at that constructor's type. -/
@[expose] def NestedMemberTableOk (m : EnvModel V env) (isProp : Bool)
    (S : Name → (Name → Nat) → (Nat → V) → V)
    (e : Name × Option ProjTable × List (ConstantVal × Nat × Nat)) : Prop :=
  ∀ (tbl : ProjTable) (cvCa : ConstantVal) (nP nF : Nat),
    e.2.1 = some tbl → e.2.2 = [(cvCa, nP, nF)] →
    ∃ (cvTa : ConstantVal) (sorts : List Level)
      (pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (Es : (Name → Nat) → List AnnotTerm),
      tbl.ctor = cvCa.name ∧ tbl.off = 1 ∧
      tbl.guards = ConLeche.structProjGuards cvCa.type nP nF sorts ∧
      TableMember m tbl.levelParams nP e.1 cvTa cvCa nF 0 tbl.structSort isProp sorts pps ds Es
        (S e.1)

/-- **A restored member's table data crosses another member's table
cons**, the per-member wrapper (`TableMember.cross`). -/
theorem NestedMemberTableOk.cross {m : EnvModel V env} {isProp : Bool}
    {S : Name → (Name → Nat) → (Nat → V) → V}
    {e : Name × Option ProjTable × List (ConstantVal × Nat × Nat)}
    (h : NestedMemberTableOk m isProp S e)
    {tbl : ProjTable} {cty : Expr} {nP' nF' : Nat}
    (hfresh : env.find? (ConstantInfo.projInfo tbl).name = none)
    (hbodies : ConLeche.structProjBodies tbl.structName nP' nF' cty = some tbl.bodies)
    (hcty : ∃ ci ∈ env.consts, ci.toConstantVal.type = cty)
    (hnpT : ∀ i, NoProjEnv env tbl.structName i)
    (hne : tbl.structName ≠ e.1)
    (m₂ : EnvModel V ⟨.projInfo tbl :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0)) :
    NestedMemberTableOk m₂ isProp S e := by
  intro tblM cvCa nP nF htblM hcs
  obtain ⟨cvTa, sorts, pps, ds, Es, hC, hoff, hg, hTM⟩ := h tblM cvCa nP nF htblM hcs
  exact ⟨cvTa, sorts, pps, ds, Es, hC, hoff, hg, hTM.cross hfresh hbodies hcty hnpT hne m₂ hac⟩

/-! ## The stage -/

/-- **The table stage at the nested route**: the run's final
environment carries an `EnvModelM` whose carrier agrees with the one it
started from at every stored name — the generic fold `stageTablesGo`
at the nested route's own inversions and `NestedMemberTableOk`. -/
theorem stageNestedTables (step : BlockTableStep V μ) {isProp : Bool}
    {S : Name → (Name → Nat) → (Nat → V) → V} :
    ∀ (l : List (Name × Option ProjTable × List (ConstantVal × Nat × Nat))) {env : Env}
      (mp : EnvModelM V μ env) {env' : Env},
      ConLeche.nestedTables (m := ConLeche.CheckM) l env = .ok env' →
      (l.map (·.1)).Nodup →
      (∀ e ∈ l, NestedMemberTableOk mp.base2 isProp S e) →
      ∃ mp' : EnvModelM V μ env', AcvalAgrees mp.base2 mp'.base2 := by
  refine stageTablesGo step (isProp := isProp) (·.1) (fun e => S e.1)
    (fun e env => ConLeche.nestedMemberTable (m := ConLeche.CheckM) e.1 e.2.1 e.2.2 env)
    (fun l env => ConLeche.nestedTables (m := ConLeche.CheckM) l env)
    (fun _ m e => NestedMemberTableOk m isProp S e) ?_ ?_ ?_ ?_
  · intro env env' h
    exact ConLeche.nestedTables_nil_inv h
  · intro a l env env' h
    obtain ⟨T, tbl?, cs⟩ := a
    exact ConLeche.nestedTables_inv h
  · intro e env env' m hok hrun
    obtain ⟨T, tbl?, cs⟩ := e
    rcases ConLeche.nestedMemberTable_inv hrun with rfl | ⟨tbl, cvCa, nP, nF, htbl?, hcs, htbl⟩
    · exact Or.inl rfl
    · obtain ⟨cvTa, sorts, pps, ds, Es, hC, hoff, hg, hTM⟩ := hok tbl cvCa nP nF htbl? hcs
      rw [hC, hoff, hg] at htbl
      exact Or.inr ⟨cvTa, cvCa, tbl.levelParams, nP, nF, 0, tbl.structSort, sorts, pps, ds, Es,
        hTM, htbl⟩
  · intro e env m tbl cty nP' nF' hok hfresh hbodies hcty hnpT hne m₂ hac
    exact hok.cross hfresh hbodies hcty hnpT hne m₂ hac

end ConLeche.Model
