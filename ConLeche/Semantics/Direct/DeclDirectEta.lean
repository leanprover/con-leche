import ConLeche.Semantics.DeclIndRun
import ConLeche.Semantics.IndBlockRun
import ConLeche.Semantics.DeclEta
import ConLeche.Verify.Extend.Inversions

import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Direct.DirectInv

/-!
# The direct-structure declaration keeps the η-families closed (task #175 wiring, W5)

The declaration fold's η half at the `.indDecl` dispatch: the modeled
arm is `declIndEtaClosedRun` (`IndBlockRun`), and the direct arm is
proved here from `DeclDirectRun`'s recorded runs — every store the
direct install performs is a **fresh cons** (`checkConstantVal`'s
duplicate guard for the three constants, `checkDirectProj`'s own
`isNone` guard for the entries), and the one former it stores carries
`directCaps`, whose `eta` slot is a literal `false`, so
`EtaFamiliesClosed.cons_nonind` applies at every step.

With this the two dispatch lemmas below make the fold's η half
**flag-agnostic**: `declStepPM` (`SetP/FoldP`) and `declEtaStep` read
the kernel's own `directParts?` dispatch and no longer consult
the former master switch (gone at W4c).
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  DirectParts fueledOps checkConstantVal
  checkDirectProjTable projTableName EtaFamiliesClosed ProjEntry)

/-! ## The stage shapes, with their freshness guards -/

/-- The table stage's run: the tower table consed at a fresh table
name (task #175 S1). -/
theorem checkDirectProjTable_shape {T C : Name}
    {lps : List Name} {nP nF : Nat} {resSort : Level}
    {guards : List Level} {off : Nat} {cvCa : ConstantVal} {env env' : Env}
    (h : checkDirectProjTable (m := ConLeche.CheckM) T C lps nP nF
      resSort guards off cvCa env = .ok env') :
    ∃ tbl : ConLeche.ProjTable, env.find? (projTableName T) = none ∧
      tbl.structName = T ∧ env' = ⟨.projInfo tbl :: env.consts⟩ := by
  obtain ⟨bodies, -, -, -, hfresh, rfl⟩ := ConLeche.checkDirectProjTable_inv h
  exact ⟨_, hfresh, rfl, rfl⟩

/-! ## The η half of the direct arm -/

/-- The table stage keeps the η-families closed: a fresh cons of a
table. -/
theorem checkDirectProjTable_etaClosed {T C : Name}
    {lps : List Name} {nP nF : Nat} {resSort : Level}
    {guards : List Level} {off : Nat} {cvCa : ConstantVal} {env env₂ : Env}
    (h : checkDirectProjTable (m := ConLeche.CheckM) T C lps nP nF
      resSort guards off cvCa env = .ok env₂)
    (hE : EtaFamiliesClosed env) : EtaFamiliesClosed env₂ := by
  obtain ⟨tbl, hfresh, hsn, rfl⟩ := checkDirectProjTable_shape h
  refine EtaFamiliesClosed.cons_nonind hE ?_ (fun _ _ heq => nomatch heq)
  show env.find? (projTableName tbl.structName) = none
  rw [hsn]; exact hfresh

end ConLeche.Semantics
