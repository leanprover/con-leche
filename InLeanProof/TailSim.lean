module

public import InLeanProof.PassRecs10
public import InLeanProof.PassTail
public import InLeanProof.DeclStep
public import InLeanProof.StepPres
/- `FEnv.push` (not exposed in `InLean/Push.lean`). -/
import all InLean.Push
import ConLeche.Verify.Cached.WalkersC
/- `ConstantInfo.name` is read as a projection of `toConstantVal`. -/
import all Lean.Declaration

/-!
# O7: the tail composed, the inductive declaration step (task #451, lane TailSim)

`tailSimI : TailSimI (PassRelI PassDataI)`: InLean's `checkBlockTailS` against
master's pure `checkBlockTail`, from the proved stages in the job's order: the
index sorts (`checkBlockIdxSortsFI_run`), the constructors' environment
(`jobEnvI_ctors`), the flush, the generated recursors (`genRecCheckI_run`), the
K flags (`streamKCheckI_run`), the generated recursors' environment
(`jobEnvI_genRecs_of_run`), the flush, the stored recursors
(`streamRecsCheckI_run`), the flush, the projection tables
(`checkBlockTablesFI_run`).  Every premise is read off the pass's relation
(`PassDataI`), moved to the stage's state by the readings' monotonicity.

`checkIndDeclC_sim`: with `passSimI` and `tailSimI`, InLean's inductive
declaration step simulates master's pure declaration kind check, from premises
P4 discharges from the declaration and the environment; the shape facts the
tail reads (`TailShapeOkI`) come from the generated entries' agreement and the
generator's projection-step check (`BlockProjBodiesOk`, `projBodiesAllOk`).
-/

@[expose] public section

namespace InLeanProof

open Lean InLean ConLeche.Cached

/-! ## Small facts -/

theorem nestKindsFlat_tr (ks : List (List (List InLean.NestFieldKind))) :
    ConLeche.nestKindsFlat (ks.map (·.map (·.map trNK))) = InLean.nestKindsFlat ks := by
  unfold ConLeche.nestKindsFlat InLean.nestKindsFlat
  simp only [List.all_map, Function.comp_def]
  congr 1; funext l; congr 1; funext l'; congr 1; funext k
  cases k <;> rfl

theorem blockNestedBit_tr (p : InLean.BlockShape) (ks : List (List (List InLean.NestFieldKind))) :
    ConLeche.blockNestedBit (trShape p) (ks.map (·.map (·.map trNK))) = InLean.blockNestedBit p ks := by
  unfold ConLeche.blockNestedBit InLean.blockNestedBit
  rw [nestKindsFlat_tr]
  simp only [trShape, trRec, List.any_map, Function.comp_def, ConLeche.BlockShape.k,
    InLean.BlockShape.k, List.length_map]
  rfl

theorem consSumCtorsF_pending (T : Lean.Name) (nP : Nat) :
    ∀ (i : Nat) (l : List (Lean.ConstantVal × Nat)) (fe : InLean.FEnv),
      (InLean.consSumCtorsF T nP i l fe).pending = fe.pending
  | _, [], _ => rfl
  | i, _ :: cs, fe => by
    unfold InLean.consSumCtorsF
    rw [consSumCtorsF_pending T nP (i + 1) cs]
    rfl

theorem consBlockCtorsF_pending (p : InLean.BlockShape) (fe : InLean.FEnv) :
    (InLean.consBlockCtorsF p fe).pending = fe.pending := by
  unfold InLean.consBlockCtorsF
  generalize fe = fe₀
  induction p.members generalizing fe₀ with
  | nil => rfl
  | cons ms rest ih => simp only [List.foldl_cons]; rw [ih, consSumCtorsF_pending]

theorem pendingFields_go_isSome {T : Lean.Name} :
    ∀ {l : List (Lean.Name × Nat)} {k : Nat}, (T, k) ∈ l →
      (InLean.FEnv.pendingFields?.go T l).isSome = true
  | (n, k') :: rest, k, h => by
    unfold InLean.FEnv.pendingFields?.go
    by_cases he : (n == T) = true
    · simp [he]
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.1 h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact absurd (beq_self_eq_true _) he
      · exact pendingFields_go_isSome h

/-- A former found at `n` is named `n` (through master's index). -/
theorem find?_ind_name {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {n : Lean.Name}
    {v : Lean.InductiveVal} (h : fe.find? n = some (.inductInfo v)) : v.name = n := by
  obtain ⟨cci, hL, hE⟩ := hP.entry n _ h
  have hn := ConLeche.Env.find?_name hL
  cases cci with
  | indInfo ccv caps =>
    obtain ⟨⟨hcn, -⟩, -⟩ := hE
    exact toName_inj (hcn ▸ hn : toName v.name = toName n)
  | _ => exact hE.elim

/-- The motives before a motive slot are fewer than all the motives. -/
theorem motive_count_lt (sx : InLean.CState) {slots : List InLean.ClassSlot} {s : Nat}
    (hs : s < slots.length) {k : InLean.ClassKey} (hk : slots.getD s default = .motive k) :
    ((List.range s).filter fun s' =>
        match slots.getD s' default with | .motive _ => true | _ => false).length <
      (ConLeche.ClassRead.motPosOf (slots.map (trSlot sx))).length := by
  unfold ConLeche.ClassRead.motPosOf
  rw [List.length_map]
  have hn : slots.length = s + (slots.length - s) := by omega
  rw [hn, List.range_add, List.filter_append, List.length_append]
  have h1 : ((List.range s).filter fun s' =>
        match slots.getD s' default with | .motive _ => true | _ => false) =
      (List.range s).filter fun s' =>
        match (slots.map (trSlot sx))[s']? with | some (.motive _) => true | _ => false := by
    apply List.filter_congr
    intro x hx
    rw [List.mem_range] at hx
    rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some, Option.map_some]
    cases slots[x] <;> rfl
  refine Nat.lt_of_le_of_lt (Nat.le_of_eq (congrArg List.length h1)) ?_
  have h2 : 0 < (((List.range (slots.length - s)).map (s + ·)).filter fun s' =>
        match (slots.map (trSlot sx))[s']? with | some (.motive _) => true | _ => false).length := by
    apply List.length_pos_of_mem (a := s)
    rw [List.mem_filter]
    refine ⟨List.mem_map.2 ⟨0, List.mem_range.2 (by omega), by simp⟩, ?_⟩
    rw [List.getElem?_map, List.getElem?_eq_getElem hs]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, Option.getD_some] at hk
    simp only [Option.map_some, hk]
    rfl
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right h2) (Nat.le_of_eq rfl)

theorem mem_formers {p : InLean.BlockShape} {cv : Lean.ConstantVal} (h : cv ∈ p.formers) :
    ∃ ms ∈ p.members, ms.cvT = cv := List.mem_map.1 h

theorem structCtor_eq {ms : InLean.MemberShape} {c : Lean.ConstantVal × Nat}
    (h : ms.structCtor? = some c) : ms.ctors = [c] := by
  unfold InLean.MemberShape.structCtor? at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; assumption
    · cases h
  · cases h

/-! ## The tail -/

/-- **The stages after the pass** (`checkBlockTailS_run`'s twin) at the pass's
relation `PassRelI PassDataI`. -/
theorem tailSimI (hC : CheckConstantValFSimI) (hRF : ReducedFormerSimI) :
    TailSimI (PassRelI PassDataI) := by
  intro block q cq Q s₀ s' hR hs hr hcl hk hQ h
  obtain ⟨⟨⟨rest, hpend⟩, hcp, hJ⟩, hpar, D⟩ := hR
  obtain ⟨env₁, p, kinds, params, rd, cls, tbl⟩ := q
  obtain ⟨cenv₁, cp, ckinds, cparams, crd, ccls, ctbl⟩ := cq
  simp only at hpend hcp hJ hpar
  subst hcp hpar
  have hkinds : ckinds = kinds.map (·.map (·.map trNK)) := D.kinds
  have hrd : crd = trCR s₀ rd := D.rd
  have hcls : ccls = cls.map (trTM s₀) := D.cls
  have htbl : ctbl = tbl.map (trNf s₀) := D.tbl
  unfold InLean.checkBlockTailS at h
  simp only at h
  -- the index sorts
  obtain ⟨_, s₁, h1, h⟩ := bindI_ok h
  have hmem : ∀ ms ∈ p.members, okC ms.cvT.type = true ∧ (trC ms.cvT.type).looseBVarsBounded 0 = true :=
    fun ms hm => ⟨(D.members ms hm).1.1, (D.members ms hm).2⟩
  obtain ⟨hs₁, ht₁, hR1⟩ := checkBlockIdxSortsFI_run hJ.ops D.sortOk hs hmem h1
  replace hR1 := hR1.runs
  -- the constructors' environment, the flush
  have hJ₂ := jobEnvI_ctors hJ p D.ctorsFresh D.ctorsNodup D.ctorsSorry
    (fun m hm c hc => (D.ctors _ (List.mem_map_of_mem hm) c hc).1) D.ctorsWF
  obtain ⟨u0, sB, hfl, h⟩ := bindI_ok h
  rw [flushI_run] at hfl
  injection hfl with hfl
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hfl
  have ht₂ : TabLe s₀ s₁.flushed := ht₁.trans TabLe.flushed
  -- the generated recursors
  obtain ⟨out, s₃, h3, h⟩ := bindI_ok h
  have hpOk : OkSL s₀ params = true := D.paramsOk
  have hfvs : FvsOk s₀ params := by
    intro f hf
    simp only [OkSL, List.all_eq_true] at hpOk
    refine ⟨hpOk f hf, ?_⟩
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hf
    obtain ⟨ty, he⟩ := D.paramsVar j (TrS s₀ f) (by simp [TrSL, hj])
    exact ⟨j, ty, he⟩
  obtain ⟨hfvs₂, hTrP⟩ := FvsOk.mono ht₂ hfvs
  have hMs : ∀ M ∈ cls, OkTM s₁.flushed M ∧
      FrameOk (TrSL s₁.flushed M.pfvs) (TrSL s₁.flushed (p.formers.map (·.type))) ∧
      (∀ a ∈ M.ds, (TrS s₁.flushed a).looseBVarsBounded 0 = true) ∧
      (∀ c ∈ M.ctors, okC c.1.type = true ∧ (trC c.1.type).looseBVarsBounded 0 = true) ∧
      ∀ t, M.member = some t → t < p.formers.length := by
    intro M hM
    have hok := D.clsOk M hM
    obtain ⟨hok₂, htr⟩ := OkTM.mono ht₂ hok
    have hfo : OkSL s₀ (p.formers.map (·.type)) = true := by
      simp only [OkSL, List.all_eq_true]
      intro e he
      obtain ⟨cv, hcv, rfl⟩ := List.mem_map.1 he
      obtain ⟨ms, hms, rfl⟩ := mem_formers hcv
      exact OkS_of_okC _ (hmem ms hms).1
    refine ⟨hok₂, ?_, fun a ha => ?_, fun c hc => ?_, fun t ht => ?_⟩
    · rw [TrSL_of_tabLe ht₂ hok.2.2.1, TrSL_of_tabLe ht₂ hfo]
      exact D.frameOk hM
    · have hoa : OkS s₀ a = true := by
        have := hok.2.1; simp only [OkSL, List.all_eq_true] at this; exact this a ha
      rw [TrS_of_tabLe ht₂ hoa]
      have hM' : trTM s₀ M ∈ ccls := hcls ▸ List.mem_map_of_mem hM
      exact (D.clsMaster _ hM').2.2 (TrS s₀ a) (List.mem_map_of_mem ha)
    · obtain ⟨c1, -, c3⟩ := D.clsCtors M hM c hc
      exact ⟨c1, c3⟩
    · have := D.clsMember M hM t ht
      simpa [InLean.BlockShape.formers] using this
  have hrc : ∀ c ∈ rd.recCls, c < cls.length := by
    intro c hc
    have := D.recCls c (by rw [hrd]; exact hc)
    simpa [hcls] using this
  have hmc : ∀ s < rd.slots.length, ∀ k, rd.slots.getD s default = .motive k →
      ((List.range s).filter fun s' =>
        match rd.slots.getD s' default with | .motive _ => true | _ => false).length < cls.length := by
    intro s hs k hk
    have h1 := motive_count_lt s₀ hs hk
    have h2 := D.motives
    rw [hrd, hcls, List.length_map] at h2
    exact h2 ▸ h1
  obtain ⟨hs₃, ht₃, hout, hnd, hRG⟩ := genRecCheckI_run hC hRF hJ₂
    (flushI_csoki hs₁.residue .verified false _) D.recs
    (fun cv hcv => by obtain ⟨ms, hms, rfl⟩ := mem_formers hcv; exact hmem ms hms)
    (fun e he => by
      obtain ⟨hok₂, -⟩ := OkNf.mono ht₂ (D.tblOk e he)
      refine ⟨hok₂, ?_⟩
      rw [TrS_of_tabLe ht₂ (D.tblOk e he).2.2]
      exact D.tblCl e he)
    hMs hfvs₂ D.paramsLen (fun x hx => OkSlot.mono ht₂ (D.slotsOk x hx)) hrc hmc h3
  -- the K flags
  obtain ⟨u1, s₄, h4, hA⟩ := bindI_ok h
  obtain ⟨hs4, hRK⟩ := streamKCheckI_run s₃ p h4
  subst s₄
  -- the generated recursors' environment, the flush
  have hclsEq : cls.map (trTM s₁.flushed) = ccls := by
    rw [hcls]; exact List.map_congr_left fun M hM => (OkTM.mono ht₂ (D.clsOk M hM)).2
  have hJG := jobEnvI_genRecs_of_run hJ₂ hRG (by rw [TrSL_length]; exact D.paramsLen)
    (fun M hM => (D.clsMaster M (hclsEq ▸ hM)).1)
    (fun M hM => (D.clsMaster M (hclsEq ▸ hM)).2.1)
    (fun c hc => by simpa using hrc c hc)
    (fun o ho => ⟨(hout o ho).1, fun r hr => ((hout o ho).2.2.1 r hr).1, (hout o ho).2.2.2.2⟩) hnd
  obtain ⟨u2, sC, hfl2, hB⟩ := bindI_ok hA
  rw [flushI_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : s₃.flushed = sC := congrArg Prod.snd hfl2
  -- the stored recursors, the flush
  obtain ⟨u3, s₅, h5, hC'⟩ := bindI_ok hB
  obtain ⟨hs₅, -, hRS⟩ := streamRecsCheckI_run hJG s₃ p.recs out
    (flushI_csoki hs₃.residue .verified false _)
    (fun rc hrc => ⟨(D.recs rc hrc).1, D.shape.rules rc hrc⟩)
    (fun g hg => ⟨(hout g hg).1, (hout g hg).2.1, (hout g hg).2.2.1, (hout g hg).2.2.2.1.2.1⟩) h5
  obtain ⟨u4, sD, hfl3, hD'⟩ := bindI_ok hC'
  rw [flushI_run] at hfl3
  injection hfl3 with hfl3
  obtain rfl : s₅.flushed = sD := congrArg Prod.snd hfl3
  -- the projection tables
  have hTM : ∀ ms ∈ p.members, TableMemberOk p.nP ms := by
    intro ms hms c hc
    have hcs := structCtor_eq hc
    refine ⟨(D.members ms hms).1.2.2 c (by rw [hcs]; exact List.mem_singleton_self c),
      fun i hi => ?_⟩
    exact D.shape.steps ms hms c hcs i hi
  obtain ⟨cQ, hcQ, hrelQ⟩ := blockTables_tr p p.members hTM hQ
  rw [ConLeche.Cached.blockTablesC_eq] at hcQ
  have hTpend : ∀ t ∈ Q, ∀ v, (InLean.consBlockCtorsF p env₁).find? t.structName =
      some (.inductInfo v) → (InLean.consBlockCtorsF p env₁).isPending v.name = true := by
    intro t ht v hv
    obtain ⟨ms, hms, hn⟩ := blockTables_mem p p.members hQ t ht
    rw [find?_ind_name hJ₂.pres hv]
    unfold InLean.FEnv.isPending InLean.FEnv.pendingFields?
    rw [consBlockCtorsF_pending, hpend, hn]
    apply pendingFields_go_isSome
    apply List.mem_append_left
    exact List.mem_map_of_mem (f := fun ms : InLean.MemberShape =>
      (ms.declared.name, match ms.ctors with | [c] => c.2 | _ => 0)) hms
  obtain ⟨rfl, hRT⟩ := checkBlockTablesCI_run hJ₂.pres hrelQ hTpend hD'
  refine ⟨hs₅.residue.flushed, ?_⟩
  have hcQ' : ConLeche.blockTables (trShape p) (trShape p).members = some cQ := hcQ
  -- master's tail
  have hRun : Runs (ConLeche.checkBlockTail (ConLeche.fueledOpsM .verified) (block.map trCI)
      ⟨cenv₁, trShape p, ckinds, params.map (TrS s₀), crd, ccls, ctbl⟩ cQ) () := by
    unfold ConLeche.checkBlockTail
    refine Runs.bind hR1 ?_
    dsimp only
    unfold ConLeche.checkBlockRec
    rw [hkinds, blockNestedBit_tr, htbl, hrd, ← hclsEq,
      show params.map (TrS s₀) = TrSL s₁.flushed params from hTrP.symm,
      show trCR s₀ rd = trCR s₁.flushed rd from (trCR_mono ht₂ D.slotsOk).symm,
      show (tbl.map (trNf s₀)).toList = tbl.toList.map (trNf s₁.flushed) by
        rw [Array.toList_map]; exact (map_trNf_mono ht₂ D.tblOk).symm]
    refine Runs.bind hRG ?_
    refine Runs.bind hRK ?_
    refine Runs.bind hRS ?_
    exact hRT
  obtain ⟨F, hF⟩ := runs_atF hRun
  rw [ConLeche.checkBlockTail_datF] at hF
  exact ⟨F, cQ, hcQ', hF⟩

/-! ## The shape facts the tail reads -/

theorem blockSplitRecs_info : ∀ {block : List Lean.ConstantInfo} {rs},
    InLean.blockSplitRecs block = some rs →
    ∀ r ∈ rs, ∃ v, Lean.ConstantInfo.recInfo v ∈ block ∧ v.rules = r.2.2.2.2
  | [], rs, h => by simp [InLean.blockSplitRecs] at h; subst h; simp
  | .recInfo v :: rest, rs, h => by
    simp only [InLean.blockSplitRecs, Option.map_eq_some_iff] at h
    obtain ⟨rs', h1, rfl⟩ := h
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨v, List.mem_cons_self, rfl⟩
    · obtain ⟨w, hw, he⟩ := blockSplitRecs_info h1 r hr
      exact ⟨w, List.mem_cons_of_mem _ hw, he⟩
  | .inductInfo _ :: _, _, h | .ctorInfo _ :: _, _, h | .axiomInfo _ :: _, _, h
  | .defnInfo _ :: _, _, h | .thmInfo _ :: _, _, h | .opaqueInfo _ :: _, _, h
  | .quotInfo _ :: _, _, h => by simp [InLean.blockSplitRecs] at h

theorem blockSplitCtors_info : ∀ {block : List Lean.ConstantInfo} {cs rs},
    InLean.blockSplitCtors block = some (cs, rs) →
    (∀ c ∈ cs, ∃ v, Lean.ConstantInfo.ctorInfo v ∈ block ∧ v.toConstantVal = c.1 ∧
      v.numFields = c.2.2) ∧
    ∀ r ∈ rs, ∃ v, Lean.ConstantInfo.recInfo v ∈ block ∧ v.rules = r.2.2.2.2
  | .ctorInfo v :: rest, cs, rs, h => by
    simp only [InLean.blockSplitCtors, Option.map_eq_some_iff] at h
    obtain ⟨q, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨ih1, ih2⟩ := blockSplitCtors_info h1
    refine ⟨fun c hc => ?_, fun r hr => ?_⟩
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨v, List.mem_cons_self, rfl, rfl⟩
      · obtain ⟨w, hw, he⟩ := ih1 c hc
        exact ⟨w, List.mem_cons_of_mem _ hw, he⟩
    · obtain ⟨w, hw, he⟩ := ih2 r hr
      exact ⟨w, List.mem_cons_of_mem _ hw, he⟩
  | [], cs, rs, h | .recInfo _ :: _, cs, rs, h | .inductInfo _ :: _, cs, rs, h
  | .axiomInfo _ :: _, cs, rs, h | .defnInfo _ :: _, cs, rs, h | .thmInfo _ :: _, cs, rs, h
  | .opaqueInfo _ :: _, cs, rs, h | .quotInfo _ :: _, cs, rs, h => by
    unfold InLean.blockSplitCtors at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨rs', h1, rfl, rfl⟩ := h
    exact ⟨by simp, blockSplitRecs_info h1⟩

theorem blockSplit_info : ∀ {block : List Lean.ConstantInfo} {cvTs cs rs},
    InLean.blockSplit block = some (cvTs, cs, rs) →
    (∀ c ∈ cs, ∃ v, Lean.ConstantInfo.ctorInfo v ∈ block ∧ v.toConstantVal = c.1 ∧
      v.numFields = c.2.2) ∧
    ∀ r ∈ rs, ∃ v, Lean.ConstantInfo.recInfo v ∈ block ∧ v.rules = r.2.2.2.2
  | .inductInfo v :: rest, cvTs, cs, rs, h => by
    simp only [InLean.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨q, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, h3⟩ := h2
    obtain ⟨q1, q2, q3⟩ := q
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    obtain ⟨ih1, ih2⟩ := blockSplit_info h1
    refine ⟨fun c hc => ?_, fun r hr => ?_⟩
    · obtain ⟨w, hw, he⟩ := ih1 c hc
      exact ⟨w, List.mem_cons_of_mem _ hw, he⟩
    · obtain ⟨w, hw, he⟩ := ih2 r hr
      exact ⟨w, List.mem_cons_of_mem _ hw, he⟩
  | [], cvTs, cs, rs, h | .recInfo _ :: _, cvTs, cs, rs, h | .ctorInfo _ :: _, cvTs, cs, rs, h
  | .axiomInfo _ :: _, cvTs, cs, rs, h | .defnInfo _ :: _, cvTs, cs, rs, h
  | .thmInfo _ :: _, cvTs, cs, rs, h | .opaqueInfo _ :: _, cvTs, cs, rs, h
  | .quotInfo _ :: _, cvTs, cs, rs, h => by
    unfold InLean.blockSplit at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨q, h1, rfl, rfl, rfl⟩ := h
    exact blockSplitCtors_info h1

/-- **A recognised shape's constructors and recursors, as the block stores
them**: a constructor's entry with its field count, a recursor's rules. -/
theorem readBlock_info {nP : Nat} {block : List Lean.ConstantInfo} {p : InLean.BlockShape}
    (h : InLean.readBlock nP block = .ok p) :
    (∀ ms ∈ p.members, ∀ c ∈ ms.ctors, ∃ v, Lean.ConstantInfo.ctorInfo v ∈ block ∧
      v.toConstantVal = c.1 ∧ v.numFields = c.2) ∧
    ∀ rc ∈ p.recs, ∃ v, Lean.ConstantInfo.recInfo v ∈ block ∧ v.rules = rc.rules := by
  cases hsp : InLean.blockSplit block with
  | none =>
    unfold InLean.readBlock at h; rw [hsp] at h; cases h
  | some q =>
    obtain ⟨cvTs, cs, rs⟩ := q
    obtain ⟨h2, h3⟩ := blockSplit_info hsp
    have hG : ∀ (names lps : List Lean.Name) (k : Nat),
        ∀ g ∈ InLean.blockGroups names lps nP k (cs.map fun c => (c.1, c.2.2)), ∀ c ∈ g,
          ∃ v, Lean.ConstantInfo.ctorInfo v ∈ block ∧ v.toConstantVal = c.1 ∧ v.numFields = c.2 := by
      intro names lps k g hg c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 (blockGroups_sub _ _ _ _ _ g hg c hc)
      exact h2 c' hc'
    unfold InLean.readBlock at h
    rw [hsp] at h
    cases cvTs with
    | nil => cases h
    | cons cvT0 tl =>
      cases rs with
      | nil => cases h
      | cons r0 rtl =>
        obtain ⟨cvR0, r0b⟩ := r0
        simp only at h
        cases hc : InLean.blockMemberCounts nP (cvT0 :: tl).length cs.length
            ((cvT0 :: tl).map (·.name)) ((cvR0, r0b) :: rtl) 0 (cvT0 :: tl) with
        | error e => rw [hc] at h; cases h
        | ok nIdxs =>
          rw [hc] at h
          simp only at h
          revert h
          repeat' split
          all_goals intro h
          all_goals first
            | (cases h; done)
            | (simp only [Except.ok.injEq] at h; subst h
               exact ⟨members_ctors_from (hG _ _ _), fun rc hrc => by
                 obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hrc; exact h3 r hr⟩)

/-- A `for` loop of `CheckCM` that ran through has run its body at every
element, each run yielding. -/
theorem forIn_ok_each {α β : Type} {P : α → Prop} {f : α → β → InLean.CheckCM (ForInStep β)}
    (hf : ∀ a b s r s', f a b s = .ok (r, s') → P a ∧ ∃ b', r = .yield b') :
    ∀ {l : List α} {b : β} {s₀ : InLean.CState} {r : β} {s' : InLean.CState},
      forIn l b f s₀ = .ok (r, s') → ∀ a ∈ l, P a
  | [], _, _, _, _, _ => by simp
  | a :: l, b, s₀, r, s', h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, s₁, h1, h2⟩ := bindI_ok h
    obtain ⟨hP, b', rfl⟩ := hf a b s₀ st s₁ h1
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hP
    · exact forIn_ok_each hf h2 x hx

/-- **The generated entries' agreement at a member**: the block stores its
former at the member's name, at the shape's parameter count and with the
member's constructors. -/
theorem genEntriesAgree_members {p : InLean.BlockShape} {block : List Lean.ConstantInfo}
    {s s' : InLean.CState} (h : InLean.genEntriesAgree p block s = .ok ((), s')) :
    ∀ ms ∈ p.members, ∃ v, InLean.constNamed? block ms.cvT.name = some (.inductInfo v) ∧
      v.numParams = p.nP ∧ v.ctors = ms.ctors.map (·.1.name) := by
  unfold InLean.genEntriesAgree at h
  obtain ⟨u, s₁, h1, -⟩ := bindI_ok h
  refine forIn_ok_each ?_ h1
  intro ms b s r s'' hf
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k : α → InLean.CheckCM (ForInStep PUnit)}
      {s : InLean.CState}, ¬ ((throw e : InLean.CheckCM α) >>= k) s = .ok (r, s'') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bindI_ok h; exact throwI_ok h1
  split at hf
  · rename_i v hv
    split at hf
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      refine ⟨⟨v, hv, hcond.1.1.1.2, hcond.1.2⟩, ?_⟩
      simp only at hf
      obtain ⟨_, _, -, h2⟩ := bindI_ok hf
      exact ⟨_, (pureI_ok h2).1.symm⟩
    · exact absurd hf hth
  · exact absurd hf hth

/-- **The projection bodies the generator's output passed**
(`projBodiesAllOk`), at the stored block: at a one-constructor former, its
constructor's every field (`projBodyOk`). -/
def BlockProjBodiesOk (block : List Lean.ConstantInfo) : Prop :=
  ∀ v, Lean.ConstantInfo.inductInfo v ∈ block → ∀ c, v.ctors = [c] →
    ∀ cv, Lean.ConstantInfo.ctorInfo cv ∈ block → cv.name = c → ∀ i < cv.numFields,
      InLean.projBodyOk v.name v.numParams i cv.type = true

theorem blockProjBodiesOk_of_projBodiesAllOk {consts : Array Lean.ConstantInfo}
    {block : List Lean.ConstantInfo} (h : InLean.projBodiesAllOk consts = true)
    (hsub : ∀ ci ∈ block, ci ∈ consts) : BlockProjBodiesOk block := by
  intro v hv c hc cv hcv hn i hi
  unfold InLean.projBodiesAllOk at h
  rw [Array.all_eq_true_iff_forall_mem] at h
  have h1 := h _ (hsub _ hv)
  simp only [hc] at h1
  rw [Array.all_eq_true_iff_forall_mem] at h1
  have h2 := h1 _ (hsub _ hcv)
  simp only [hn, bne_self_eq_false, Bool.false_or, List.all_eq_true, List.mem_range] at h2
  exact h2 i hi

/-- **`BlockProjBodiesOk` of the stored block**, from the inductive check's
`projBodiesAllOk` on the generator's output. -/
theorem blockProjBodiesOk_storedBlock {consts : Array Lean.ConstantInfo}
    (h : InLean.projBodiesAllOk consts = true) : BlockProjBodiesOk (InLean.storedBlock consts) :=
  blockProjBodiesOk_of_projBodiesAllOk h fun ci hci => by
    unfold InLean.storedBlock at hci
    simp only [Array.toList_append, List.mem_append, Array.mem_toList_iff, Array.mem_filter] at hci
    rcases hci with (h | h) | h <;> exact h.1

/-- **The shape facts the tail reads** (`TailShapeOkI`), from the block's
record, the generator's projection bodies and the generated entries' agreement. -/
theorem tailShapeOkI_of {nP : Nat} {block : List Lean.ConstantInfo}
    {cb : List ConLeche.ConstantInfo} (hb : toBlock block = some cb)
    (hr : ∀ ci ∈ block, CIRange ci) (hst : BlockProjBodiesOk block)
    {p : InLean.BlockShape} {s : InLean.CState} (hsh : InLean.readBlock nP block = .ok p)
    (hg : InLean.genEntriesAgree p block s = .ok ((), s)) : TailShapeOkI p := by
  obtain ⟨hci, hrc⟩ := readBlock_info hsh
  have hok := toBlock_CIOk hb hr
  refine ⟨fun ms hms c hc i hi => ?_, fun rc hrc' r hr' => ?_⟩
  · obtain ⟨v, hv, hnP, hvc⟩ := genEntriesAgree_members hg ms hms
    obtain ⟨hvm, hvn⟩ := constNamed?_mem hv
    obtain ⟨cv, hcv, hcve, hnf⟩ := hci ms hms c (by rw [hc]; exact List.mem_singleton_self c)
    have hst' := hst v hvm c.1.name (by simp [hvc, hc]) cv hcv (by rw [← hcve]) i
      (by omega)
    have hty : cv.type = c.1.type := by rw [← hcve]
    have hvn' : v.name = ms.cvT.name := hvn
    rw [hvn', hnP, hty] at hst'
    rw [((readBlock_members hsh) ms hms).1]
    exact hst'
  · obtain ⟨v, hv, hrl⟩ := hrc rc hrc'
    exact (hok _ hv).2 r (hrl ▸ hr')

/-! ## The inductive declaration step -/

variable {pins : List ConLeche.NatOpPinSet}

/-- **O7: InLean's inductive declaration simulates master's pure declaration
kind check** on the translated block, from premises on the declaration and
the environment alone: the job's environment relation (`JobEnvI`), `sorryAx`
only under `coreAxioms`, the residue, the block in range and closed
(`constInRange`, `constClosed`), its projection bodies (`projBodiesAllOk`,
`blockProjBodiesOk_storedBlock`) and its record (`toBlock`). -/
theorem checkIndDeclC_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {block : List Lean.ConstantInfo} {cb : List ConLeche.ConstantInfo} {nP : Nat}
    (hso : ∀ ci ∈ block, ci.name = InLean.sorryAxName → fe.coreAxioms = true)
    {s₀ s' : InLean.CState} (hs : CSOKIF s₀) (hr : ∀ ci ∈ block, CIRange ci)
    (hcl : ∀ ci ∈ block, CIClosed ci) (hst : BlockProjBodiesOk block) (hb : toBlock block = some cb)
    (h : InLean.checkIndDeclC .verified fe block nP s₀ = .ok ((), s')) :
    CSOKIF s' ∧ ∃ F L', ConLeche.checkDeclKind (ConLeche.fueledOps .verified F) pins L
      (.indDecl cb nP) = .ok L' :=
  checkIndDeclC_sim_stages checkConstantValFSimI reducedFormerSimI
    (passSimI checkConstantValFSimI reducedFormerSimI)
    (tailSimI checkConstantValFSimI reducedFormerSimI) hJ hso hs hr hcl hb
    (fun _ _ hsh hg => tailShapeOkI_of hb hr hst hsh hg) h

end InLeanProof
