module

public import ConLeche.Semantics.Inductives.DeclBlockEta
public import ConLeche.Verify.EnvGuards
public import ConLeche.Semantics.Inductives.DeclBlock
import ConLeche.Kernel.Inductives.FieldTele
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.RecStageRun

@[expose] public section

/-!
# The uniform install keeps the η-families closed: the whole run

`declBlockRun_etaClosed`: the stage lemmas of `DeclBlockEta.lean`
composed along the install's run record (`DeclBlockRun`), whose
recursor stage is read through the target check's producer
(`recStage_of_targetG`, `RecStageRun.lean`).
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  fueledOps checkConstantVal
  checkStructProjTable projTableName EtaFamiliesClosed ProjEntry)

/-! ## The whole run -/

/-- **The uniform install keeps the η-families closed, at k members**,
from the run record alone, at every setting of both gates. -/
theorem declBlockRun_etaClosed {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p₀ : BlockParts} (hE : EtaFamiliesClosed env)
    (h : DeclBlockRun μ F env block p₀ env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨hndC, -, isRec, env₁, cvTas, p₁, p, ctorsAs, sortsss, isorts, rs,
    hInd, hp, hCtors, -, -, -, hRec, hTbl⟩ := h
  subst hp
  obtain ⟨_, _, _, _, _, -, -, hp₁, rfl, -, -, -⟩ := ConLeche.checkBlockInds_shape hInd
  have hlenCv : cvTas.length = p₁.members.length := by
    rw [ConLeche.checkBlockInds_length hInd, hp₁]; rfl
  -- the three freshness facts and the stored constructors' names
  have hfT := checkBlockInds_fresh hInd
  obtain ⟨hnames₀, hfC⟩ := checkBlockCtors_names hCtors
  have hnames : ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
      = p₁.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) := by
    have hz : (p₁.members.zip cvTas).map Prod.fst = p₁.members :=
      List.map_fst_zip (Nat.le_of_eq hlenCv.symm)
    calc _ = ((p₁.members.zip cvTas).map Prod.fst).map
            (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) := by
          rw [hnames₀, List.map_map]; rfl
      _ = _ := by rw [hz]
  have hndAll : ((ctorsAs.map (·.map (·.1.name))).flatten).Nodup := by
    have hmap : ctorsAs.map (·.map (·.1.name))
        = p₁.members.map (fun ms => ms.ctors.map (·.1.name)) := by
      have := congrArg (List.map (List.map Prod.fst)) hnames
      simpa [List.map_map, Function.comp_def] using this
    have hall : p₁.allCtors = p₀.allCtors := by
      rw [hp₁]; rfl
    rw [hmap]
    have : p₁.allCtors.map (·.1.name)
        = (p₁.members.map (fun ms => ms.ctors.map (·.1.name))).flatten := by
      rw [ConLeche.BlockShape.allCtors, List.map_flatten, List.map_map]
      rfl
    rw [← this, hall]
    exact hndC
  -- ## the constructors' environment is closed
  have hEC : EtaFamiliesClosed (consBlockCtors p₁.nP ctorsAs
      (consBlockInds p₁ isRec cvTas 0 env)) := by
    intro T cvT caps hf he hr
    have hf₁ := consBlockCtors_find?_indInfo hf
    rcases ConLeche.find?_consBlockInds_indInfo hf₁ with ⟨j, hj, -, hcaps⟩ | hf₀
    · -- a member of the block: its one constructor is stored
      subst hcaps
      rw [Nat.zero_add] at he ⊢
      have hjl : j < p₁.members.length := by
        rw [← hlenCv]; exact (List.getElem?_eq_some_iff.mp hj).1
      have hgetD : p₁.members.getD j default = p₁.members[j] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
      have hj' : (ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2))))[j]?
          = some (p₁.members[j].ctors.map (fun c => (c.1.name, c.2))) := by
        rw [hnames, List.getElem?_map, List.getElem?_eq_getElem hjl]; rfl
      rw [List.getElem?_map] at hj'
      obtain ⟨ctorsA, hcA, hcAeq⟩ := Option.map_eq_some_iff.mp hj'
      match hcs : p₁.members[j].ctors with
      | [c] =>
        rw [hcs] at hcAeq
        match ctorsA, hcAeq with
        | [cA], hcAeq =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
            and_true] at hcAeq
          refine ⟨cA.1, ?_⟩
          rw [blockCapsAt, hgetD, hcs]
          show (consBlockCtors p₁.nP ctorsAs (consBlockInds p₁ isRec cvTas 0 env)).find? c.1.name
            = some (.ctorInfo cA.1 p₁.nP c.2)
          rw [← hcAeq.1, ← hcAeq.2]
          exact consBlockCtors_find?_mem hndAll (List.mem_of_getElem? hcA) List.mem_cons_self
        | [], hcAeq => simp at hcAeq
        | _ :: _ :: _, hcAeq => simp at hcAeq
      | [] => rw [blockCapsAt, hgetD, hcs] at he; exact nomatch he
      | _ :: _ :: _ => rw [blockCapsAt, hgetD, hcs] at he; exact nomatch he
    · -- a family stored before the block: its η constructor reads through
      obtain ⟨cvC, hfC₀⟩ := hE T cvT caps hf₀ he hr
      refine ⟨cvC, ?_⟩
      have hf₁C : (consBlockInds p₁ isRec cvTas 0 env).find? caps.etaCtor
          = some (.ctorInfo cvC caps.etaParams caps.etaFields) := by
        rw [consBlockInds_find?_of_ne]
        · exact hfC₀
        · intro cv hcv hh
          have := hfT cv hcv
          rw [hh, hfC₀] at this
          exact nomatch this
      rw [consBlockCtors_find?_of_ne]
      · exact hf₁C
      · intro A hA hmem
        obtain ⟨cA, hcA, hn⟩ := List.mem_map.mp hmem
        have := hfC A hA cA hcA
        rw [hn, hf₁C] at this
        exact nomatch this
  -- ## the recursors (at their majors), then the tables
  obtain ⟨_, _, R, -⟩ := ConLeche.checkBlockRec_run hRec
  have hS := ConLeche.recStage_of_targetG R (ConLeche.ctorsLen_of_names hnames)
  refine checkBlockTables_etaClosed ?_ hTbl
  exact EtaFamiliesClosed.keep hEC
    (consBlockRecsT_extEta (ExtEta.refl _) fun r hr => (ConLeche.recStage_cvFacts hS r hr).1)

end ConLeche.Semantics
