module

public import InLeanProof.IndBlockKS
/- `ConstantInfo.name` is read as the projection of `toConstantVal`. -/
import all Lean.Declaration

/-!
# What an accepted recognised block says (task #451, lane P3r)

The facts `BlockPresObl`'s recognised branch reads off InLean's accepted run,
functionally (`bindI_ok`), without the walks' simulation:

* `genEntriesAgree_facts`: every member's former, every constructor and every
  recursor of the shape has a generated entry carrying what con-leche's
  install computes (`GenAgree`).
* `checkBlockKS_cover`: the block check's recursor-name stage
  (`targetRecPins`, the first step of `genRecCheck`) compares the shape's
  constructor grouping with the block's constructors, so every constructor
  of the block is in exactly one member's group, in order; and the members'
  and recursors' counts are the block's.  The stages in front of it
  (`reduceMembersS`, `checkBlockPassS`, `checkBlockIdxSortsF`) keep the
  shape's constructors and recursors.
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## Runs: loops and guards -/

/-- **A `for` loop that accepted**: every element's body accepted (from some
state), given that an accepting body always continues. -/
theorem forIn_facts {α : Type} {P : α → Prop} {f : α → PUnit → InLean.CheckCM (ForInStep PUnit)}
    (hf : ∀ x s r s', f x PUnit.unit s = .ok (r, s') → P x ∧ r = .yield PUnit.unit) :
    ∀ (l : List α) (s s' : InLean.CState), (forIn l PUnit.unit f) s = .ok (PUnit.unit, s') →
      ∀ x ∈ l, P x := by
  intro l
  induction l with
  | nil => intro _ _ _ x hx; cases hx
  | cons a l ih =>
    intro s s' h x hx
    rw [List.forIn_cons] at h
    obtain ⟨r, s₁, h1, h2⟩ := bindI_ok h
    obtain ⟨hPa, rfl⟩ := hf a s r s₁ h1
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hPa
    · exact ih s₁ s' h2 x hx

/-- A guard `unless c do throw e` with its continuation, accepted. -/
theorem iteJ_ok {β : Type} {c : Prop} [Decidable c] {jp : PUnit → InLean.CheckCM β}
    {e : InLean.CheckError} {s : InLean.CState} {v : β} {s' : InLean.CState}
    (h : (if c then jp PUnit.unit else (throw e >>= jp)) s = .ok (v, s')) :
    c ∧ jp PUnit.unit s = .ok (v, s') := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h; exact ⟨hc, h⟩
  · simp only [hc, ↓reduceIte] at h
    obtain ⟨_, _, h1, _⟩ := bindI_ok h
    exact (throwI_ok h1).elim

/-- A guard `if c then pure x else throw e`, accepted. -/
theorem itePure_ok {β : Type} {c : Prop} [Decidable c] {x : β}
    {e : InLean.CheckError} {s : InLean.CState} {v : β} {s' : InLean.CState}
    (h : (if c then pure x else throw e : InLean.CheckCM β) s = .ok (v, s')) : c ∧ x = v := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h; exact ⟨hc, (pureI_ok h).1⟩
  · simp only [hc, ↓reduceIte] at h; exact (throwI_ok h).elim

/-! ## The generated entries -/

/-- **What `genEntriesAgree` checks**, as propositions: the former, each
constructor and each recursor of the shape found in the block (first by
name, `constNamed?`) with the data con-leche's install computes. -/
structure GenAgree (p : InLean.BlockShape) (block : List Lean.ConstantInfo) : Prop where
  former : ∀ ms ∈ p.members, ∃ v, constNamed? block ms.cvT.name = some (.inductInfo v) ∧
    v.all = p.memberNames ∧ v.numParams = p.nP ∧ v.numIndices = ms.nIdx ∧
    v.ctors = ms.ctors.map (·.1.name) ∧ v.isRec = blockIsRec p
  ctor : ∀ ms ∈ p.members, ∀ c ∈ ms.ctors, ∃ v, constNamed? block c.1.name = some (.ctorInfo v) ∧
    v.numParams = p.nP ∧ v.numFields = c.2 ∧ v.induct = ms.cvT.name
  recs : ∀ rc ∈ p.recs, ∃ v, constNamed? block rc.cvR.name = some (.recInfo v) ∧
    v.all = p.memberNames

/-- **An accepted `genEntriesAgree` gives `GenAgree`.** -/
theorem genEntriesAgree_facts {p : InLean.BlockShape} {block : List Lean.ConstantInfo}
    {s s' : InLean.CState} (h : (genEntriesAgree p block) s = .ok ((), s')) : GenAgree p block := by
  unfold genEntriesAgree at h
  obtain ⟨u1, s₁, h1, h2⟩ := bindI_ok h
  obtain ⟨u2, s₂, h3, -⟩ := bindI_ok h2
  -- the members' loop
  have hM := forIn_facts (P := fun ms => (∃ v, constNamed? block ms.cvT.name = some (.inductInfo v) ∧
      v.all = p.memberNames ∧ v.numParams = p.nP ∧ v.numIndices = ms.nIdx ∧
      v.ctors = ms.ctors.map (·.1.name) ∧ v.isRec = blockIsRec p) ∧
      ∀ c ∈ ms.ctors, ∃ v, constNamed? block c.1.name = some (.ctorInfo v) ∧
        v.numParams = p.nP ∧ v.numFields = c.2 ∧ v.induct = ms.cvT.name) ?_ p.members s s₁ h1
  · -- the recursors' loop
    have hR := forIn_facts (P := fun rc => ∃ v, constNamed? block rc.cvR.name = some (.recInfo v) ∧
        v.all = p.memberNames) ?_ p.recs s₁ s₂ h3
    · exact ⟨fun ms hms => (hM ms hms).1, fun ms hms => (hM ms hms).2, hR⟩
    · intro rc s r s' hb
      cases hk : constNamed? block rc.cvR.name with
      | none =>
        simp only [hk] at hb
        obtain ⟨_, _, hb1, _⟩ := bindI_ok hb
        exact (throwI_ok hb1).elim
      | some ci =>
        cases ci with
        | recInfo v =>
          simp only [hk] at hb
          obtain ⟨hc, hr⟩ := itePure_ok hb
          exact ⟨⟨v, rfl, by simpa using hc⟩, hr.symm⟩
        | _ =>
          simp only [hk] at hb
          obtain ⟨_, _, hb1, _⟩ := bindI_ok hb
          exact (throwI_ok hb1).elim
  · intro ms s r s' hb
    have hctor : ∀ s₃ s₄, (forIn ms.ctors PUnit.unit fun (x : ConstantVal × Nat) (_ : PUnit) =>
        match x with
        | (c, nF) =>
          match constNamed? block c.name with
          | some (ConstantInfo.ctorInfo v) =>
            if (v.numParams == p.nP && v.numFields == nF && v.induct == ms.cvT.name) = true then
              (pure (ForInStep.yield PUnit.unit) : InLean.CheckCM (ForInStep PUnit))
            else do
              throw (InLean.CheckError.internal
                (toString "inductive generator: " ++ toString c.name ++
                  toString "'s entry is not the block's"))
              pure (ForInStep.yield PUnit.unit)
          | _ => do
            throw (InLean.CheckError.internal
              (toString "inductive generator: no constructor " ++ toString c.name))
            pure (ForInStep.yield PUnit.unit)) s₃ = .ok (PUnit.unit, s₄) →
        ∀ c ∈ ms.ctors, ∃ v, constNamed? block c.1.name = some (.ctorInfo v) ∧
          v.numParams = p.nP ∧ v.numFields = c.2 ∧ v.induct = ms.cvT.name := by
      intro s₃ s₄ hl
      refine forIn_facts ?_ ms.ctors s₃ s₄ hl
      intro c s r s' hc'
      obtain ⟨c, nF⟩ := c
      cases hk : constNamed? block c.name with
      | none =>
        simp only [hk] at hc'
        obtain ⟨_, _, hc1, _⟩ := bindI_ok hc'
        exact (throwI_ok hc1).elim
      | some ci =>
        cases ci with
        | ctorInfo cv =>
          simp only [hk] at hc'
          obtain ⟨hcc, hr⟩ := itePure_ok hc'
          simp only [Bool.and_eq_true, beq_iff_eq] at hcc
          exact ⟨⟨cv, rfl, hcc.1.1, hcc.1.2, hcc.2⟩, hr.symm⟩
        | _ =>
          simp only [hk] at hc'
          obtain ⟨_, _, hc1, _⟩ := bindI_ok hc'
          exact (throwI_ok hc1).elim
    cases hk : constNamed? block ms.cvT.name with
    | none =>
      simp only [hk] at hb
      obtain ⟨_, _, hb1, _⟩ := bindI_ok hb
      exact (throwI_ok hb1).elim
    | some ci =>
      cases ci with
      | inductInfo v =>
        simp only [hk] at hb
        obtain ⟨hc, hb⟩ := iteJ_ok hb
        obtain ⟨u, s₃, hb1, hb2⟩ := bindI_ok hb
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact ⟨⟨⟨v, rfl, hc.1.1.1.1, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩,
          hctor s s₃ (by cases u; exact hb1)⟩, (pureI_ok hb2).1.symm⟩
      | _ =>
        simp only [hk] at hb
        obtain ⟨_, _, hb1, _⟩ := bindI_ok hb
        exact (throwI_ok hb1).elim

/-! ## The block check's constructor grouping -/

section
variable {μ : CheckMode} {fe : InLean.FEnv}

theorem checkBlockIndsF_shape {ops : InLean.CheckerOps} {p : InLean.BlockShape} {isRec : Bool}
    {r : InLean.FEnv × InLean.BlockShape} {s s' : InLean.CState}
    (h : (checkBlockIndsF ops fe p isRec) s = .ok (r, s')) :
    r.2.members = p.members ∧ r.2.recs = p.recs := by
  unfold checkBlockIndsF at h
  cases hm : p.members with
  | nil => simp only [hm] at h; exact (throwI_ok h).elim
  | cons ms0 rest =>
    simp only [hm] at h
    obtain ⟨_, _, -, h⟩ := bindI_ok h
    obtain ⟨_, _, -, h⟩ := bindI_ok h
    obtain ⟨_, _, -, h⟩ := bindI_ok h
    rw [← (pureI_ok h).1]
    simp [InLean.BlockShape.withSort, hm]

theorem checkBlockPassS_shape {p : InLean.BlockShape} {isRec : Bool} {q : InLean.BlockPass}
    {s s' : InLean.CState} (h : (checkBlockPassS μ fe p isRec) s = .ok (q, s')) :
    q.p.members = p.members ∧ q.p.recs = p.recs := by
  unfold checkBlockPassS at h
  obtain ⟨⟨fe₁, p₁⟩, _, h1, h⟩ := bindI_ok h
  have hp := checkBlockIndsF_shape h1
  repeat (obtain ⟨_, _, -, h⟩ := bindI_ok h)
  rw [← (pureI_ok h).1]
  exact hp

/-- What the recursor-name stage checks of the block's split. -/
theorem targetRecPins_split {p : InLean.BlockShape} {block : List Lean.ConstantInfo}
    {s s' : InLean.CState} (h : (targetRecPins p block) s = .ok ((), s')) :
    ∃ cvTs cs rs, InLean.blockSplit block = some (cvTs, cs, rs) ∧ cvTs.length = p.k ∧
      rs.length = p.recs.length ∧ p.allCtors.map (·.1.name) = cs.map (·.1.name) := by
  unfold targetRecPins at h
  obtain ⟨-, h⟩ := iteJ_ok h
  obtain ⟨-, h⟩ := iteJ_ok h
  obtain ⟨-, h⟩ := iteJ_ok h
  obtain ⟨-, h⟩ := iteJ_ok h
  obtain ⟨-, h⟩ := iteJ_ok h
  cases hs : InLean.blockSplit block with
  | none => simp only [hs] at h; exact (throwI_ok h).elim
  | some q =>
    obtain ⟨cvTs, cs, rs⟩ := q
    simp only [hs] at h
    obtain ⟨hc, -⟩ := itePure_ok h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨cvTs, cs, rs, rfl, hc.1.1, hc.1.2, hc.2⟩

theorem checkBlockTailS_pins {block : List Lean.ConstantInfo} {q : InLean.BlockPass}
    {Q : List InLean.ProjTable} {s s' : InLean.CState}
    (h : (checkBlockTailS μ block q Q) s = .ok ((), s')) :
    ∃ s₁ s₂, (targetRecPins q.p block) s₁ = .ok ((), s₂) := by
  obtain ⟨env₁, p, kinds, params, rd, cls, tbl⟩ := q
  unfold checkBlockTailS at h
  obtain ⟨_, _, -, h⟩ := bindI_ok h
  obtain ⟨_, _, -, h⟩ := bindI_ok h
  obtain ⟨_, _, h, -⟩ := bindI_ok h
  unfold genRecCheck at h
  obtain ⟨u, s₂, h, -⟩ := bindI_ok h
  exact ⟨_, _, by cases u; exact h⟩

/-- **The block check's projection tables are built**: an accepted
`checkBlockKS` built every structure member's table (`blockTables`). -/
theorem checkBlockKS_tables {block : List Lean.ConstantInfo} {p : InLean.BlockShape}
    {s s' : InLean.CState} (h : (checkBlockKS μ fe block p) s = .ok ((), s')) :
    (InLean.blockTables p p.members).isSome := by
  unfold checkBlockKS at h
  obtain ⟨-, h⟩ := iteJ_ok h
  obtain ⟨-, h⟩ := iteJ_ok h
  obtain ⟨_, _, -, h⟩ := bindI_ok h
  obtain ⟨_, _, -, h⟩ := bindI_ok h
  obtain ⟨_, _, -, h⟩ := bindI_ok h
  obtain ⟨Q, _, hQ, -⟩ := bindI_ok h
  rw [(unwrapOrI_run hQ).1]
  rfl

/-- **The block check's constructor grouping**: an accepted `checkBlockKS`
splits the block into as many formers as the shape has members, as many
recursors as it has, and the constructors the shape's groups list, in
order. -/
theorem checkBlockKS_cover {block : List Lean.ConstantInfo} {p : InLean.BlockShape}
    {s s' : InLean.CState} (h : (checkBlockKS μ fe block p) s = .ok ((), s')) :
    ∃ cvTs cs rs, InLean.blockSplit block = some (cvTs, cs, rs) ∧ cvTs.length = p.members.length ∧
      rs.length = p.recs.length ∧ p.allCtors.map (·.1.name) = cs.map (·.1.name) ∧
      (p.allCtors.map (·.1.name)).Nodup ∧ p.memberNames.Nodup := by
  unfold checkBlockKS at h
  obtain ⟨hnd, h⟩ := iteJ_ok h
  obtain ⟨-, h⟩ := iteJ_ok h
  obtain ⟨ms, _, h1, h⟩ := bindI_ok h
  obtain ⟨_, _, -, h⟩ := bindI_ok h
  obtain ⟨q, _, h2, h⟩ := bindI_ok h
  obtain ⟨_, _, -, h⟩ := bindI_ok h
  have hms := reduceMembersS_ctors h1
  have hq := checkBlockPassS_shape h2
  obtain ⟨_, _, h3⟩ := checkBlockTailS_pins h
  obtain ⟨cvTs, cs, rs, hs, h4, h5, h6⟩ := targetRecPins_split h3
  simp only [Bool.and_eq_true] at hnd
  have hall : q.p.allCtors = p.allCtors := by
    simp only [InLean.BlockShape.allCtors, hq.1]
    rw [show List.map (·.ctors) ms = List.map (·.ctors) p.members from hms]
  refine ⟨cvTs, cs, rs, hs, ?_, ?_, ?_, List.Pairwise.of_map toName (fun a b h he => h (he ▸ rfl)) ((namesNodup_iff _).1 hnd.1), ?_⟩
  · rw [h4, InLean.BlockShape.k, hq.1]
    simpa using congrArg List.length hms
  · rw [h5, hq.2]
  · rw [← hall]; exact h6
  · exact List.Pairwise.of_map toName (fun a b h he => h (he ▸ rfl)) ((namesNodup_iff _).1 hnd.2)

end

/-! ## The recognised shape, spelled out -/

/-- The member records `readBlock` builds. -/
@[expose] def mkMembers (cvTs : List ConstantVal) (nIdxs : List Nat)
    (groups : List (List (ConstantVal × Nat))) : List InLean.MemberShape :=
  ((cvTs.zip nIdxs).zip groups).map fun a =>
    ({ cvT := a.1.1, declared := a.1.1, nIdx := a.1.2, ctors := a.2 } : InLean.MemberShape)

/-- The recursor records `readBlock` builds. -/
@[expose] def mkRec (names : List Name) (r : RecParts) : InLean.RecShape :=
  { cvR := r.1, rP := r.2.2.1, mI := r.2.1, tgt := recTargetOf names r.2.1 r.1.type,
    rules := r.2.2.2.2, isK := r.2.2.2.1 }

/-- **What `readBlock` builds**: the split's formers zipped with their index
counts and constructor groups, the split's recursors with their targets, the
declared parameter count, every former at the first one's level names. -/
theorem readBlock_spec {nPd : Nat} {block : List Lean.ConstantInfo} {p : InLean.BlockShape}
    (h : InLean.readBlock nPd block = .ok p) :
    ∃ cvT0 tl cs rs nIdxs, InLean.blockSplit block = some (cvT0 :: tl, cs, rs) ∧ p.nP = nPd ∧
      p.members = mkMembers (cvT0 :: tl) nIdxs (blockGroups ((cvT0 :: tl).map (·.name))
        cvT0.levelParams nPd (cvT0 :: tl).length (cs.map fun c => (c.1, c.2.2))) ∧
      p.recs = rs.map (mkRec ((cvT0 :: tl).map (·.name))) ∧
      ∀ c ∈ cvT0 :: tl, c.levelParams = cvT0.levelParams := by
  cases hsp : InLean.blockSplit block with
  | none => unfold InLean.readBlock at h; rw [hsp] at h; cases h
  | some q =>
    obtain ⟨cvTs, cs, rs⟩ := q
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
        cases hc : InLean.blockMemberCounts nPd (cvT0 :: tl).length cs.length
            ((cvT0 :: tl).map (·.name)) ((cvR0, r0b) :: rtl) 0 (cvT0 :: tl) with
        | error e => rw [hc] at h; cases h
        | ok nIdxs =>
          rw [hc] at h
          simp only at h
          cases hf : (cvT0 :: tl).find? (fun c => c.levelParams != cvT0.levelParams) with
          | some c => rw [hf] at h; cases h
          | none =>
            rw [hf] at h
            have hlps : ∀ c ∈ cvT0 :: tl, c.levelParams = cvT0.levelParams := by
              intro c hc'
              simpa using List.find?_eq_none.1 hf c hc'
            refine ⟨cvT0, tl, cs, (cvR0, r0b) :: rtl, nIdxs, rfl, ?_⟩
            revert h
            repeat' split
            all_goals intro h
            all_goals first
              | (cases h; done)
              | (simp only [Except.ok.injEq] at h; subst h
                 exact ⟨rfl, rfl, rfl, hlps⟩)

/-! ## The block's split, element by element -/

theorem blockSplitRecs_names : ∀ {block : List Lean.ConstantInfo} {rs},
    InLean.blockSplitRecs block = some rs → block.map (·.name) = rs.map (·.1.name)
  | [], rs, h => by simp [InLean.blockSplitRecs] at h; subst h; rfl
  | .recInfo v :: rest, rs, h => by
    simp only [InLean.blockSplitRecs, Option.map_eq_some_iff] at h
    obtain ⟨rs', h1, rfl⟩ := h
    simp only [List.map_cons, blockSplitRecs_names h1]; rfl
  | .inductInfo _ :: _, _, h | .ctorInfo _ :: _, _, h | .axiomInfo _ :: _, _, h
  | .defnInfo _ :: _, _, h | .thmInfo _ :: _, _, h | .opaqueInfo _ :: _, _, h
  | .quotInfo _ :: _, _, h => by simp [InLean.blockSplitRecs] at h

theorem blockSplitCtors_names : ∀ {block : List Lean.ConstantInfo} {cs rs},
    InLean.blockSplitCtors block = some (cs, rs) →
      block.map (·.name) = cs.map (·.1.name) ++ rs.map (·.1.name)
  | .ctorInfo v :: rest, cs, rs, h => by
    simp only [InLean.blockSplitCtors, Option.map_eq_some_iff] at h
    obtain ⟨q, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    simp only [List.map_cons, blockSplitCtors_names h1, List.cons_append]; rfl
  | [], cs, rs, h | .recInfo _ :: _, cs, rs, h | .inductInfo _ :: _, cs, rs, h
  | .axiomInfo _ :: _, cs, rs, h | .defnInfo _ :: _, cs, rs, h | .thmInfo _ :: _, cs, rs, h
  | .opaqueInfo _ :: _, cs, rs, h | .quotInfo _ :: _, cs, rs, h => by
    unfold InLean.blockSplitCtors at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨q, h1, rfl, rfl⟩ := h
    simp [blockSplitRecs_names h1]

/-- **The block's names are the split's**, in order. -/
theorem blockSplit_names : ∀ {block : List Lean.ConstantInfo} {cvTs cs rs},
    InLean.blockSplit block = some (cvTs, cs, rs) →
      block.map (·.name) = cvTs.map (·.name) ++ cs.map (·.1.name) ++ rs.map (·.1.name)
  | .inductInfo v :: rest, cvTs, cs, rs, h => by
    simp only [InLean.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨q, h1, h2⟩ := h
    obtain ⟨q1, q2, q3⟩ := q
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp only [List.map_cons, blockSplit_names h1, List.cons_append]; rfl
  | [], cvTs, cs, rs, h | .recInfo _ :: _, cvTs, cs, rs, h | .ctorInfo _ :: _, cvTs, cs, rs, h
  | .axiomInfo _ :: _, cvTs, cs, rs, h | .defnInfo _ :: _, cvTs, cs, rs, h
  | .thmInfo _ :: _, cvTs, cs, rs, h | .opaqueInfo _ :: _, cvTs, cs, rs, h
  | .quotInfo _ :: _, cvTs, cs, rs, h => by
    unfold InLean.blockSplit at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨q, h1, rfl, rfl, rfl⟩ := h
    simp [blockSplitCtors_names h1]

theorem blockSplitRecs_mem : ∀ {block : List Lean.ConstantInfo} {rs},
    InLean.blockSplitRecs block = some rs → ∀ ci ∈ block, ∃ v, ci = .recInfo v ∧
      (v.toConstantVal, majorIdxOf v, rulePrefixOf v, v.k, v.rules) ∈ rs
  | [], rs, _ => by simp
  | .recInfo v :: rest, rs, h => by
    simp only [InLean.blockSplitRecs, Option.map_eq_some_iff] at h
    obtain ⟨rs', h1, rfl⟩ := h
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · exact ⟨v, rfl, List.mem_cons_self⟩
    · obtain ⟨w, hw, hm⟩ := blockSplitRecs_mem h1 ci hci
      exact ⟨w, hw, List.mem_cons_of_mem _ hm⟩
  | .inductInfo _ :: _, _, h | .ctorInfo _ :: _, _, h | .axiomInfo _ :: _, _, h
  | .defnInfo _ :: _, _, h | .thmInfo _ :: _, _, h | .opaqueInfo _ :: _, _, h
  | .quotInfo _ :: _, _, h => by simp [InLean.blockSplitRecs] at h

theorem blockSplitCtors_mem : ∀ {block : List Lean.ConstantInfo} {cs rs},
    InLean.blockSplitCtors block = some (cs, rs) → ∀ ci ∈ block,
      (∃ v, ci = .ctorInfo v ∧ (v.toConstantVal, v.numParams, v.numFields) ∈ cs) ∨
      (∃ v, ci = .recInfo v ∧ (v.toConstantVal, majorIdxOf v, rulePrefixOf v, v.k, v.rules) ∈ rs)
  | .ctorInfo v :: rest, cs, rs, h => by
    simp only [InLean.blockSplitCtors, Option.map_eq_some_iff] at h
    obtain ⟨q, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · exact .inl ⟨v, rfl, List.mem_cons_self⟩
    · rcases blockSplitCtors_mem h1 ci hci with ⟨w, hw, hm⟩ | hr
      · exact .inl ⟨w, hw, List.mem_cons_of_mem _ hm⟩
      · exact .inr hr
  | [], cs, rs, h | .recInfo _ :: _, cs, rs, h | .inductInfo _ :: _, cs, rs, h
  | .axiomInfo _ :: _, cs, rs, h | .defnInfo _ :: _, cs, rs, h | .thmInfo _ :: _, cs, rs, h
  | .opaqueInfo _ :: _, cs, rs, h | .quotInfo _ :: _, cs, rs, h => by
    unfold InLean.blockSplitCtors at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨q, h1, rfl, rfl⟩ := h
    intro ci hci
    exact .inr (blockSplitRecs_mem h1 ci hci)

/-- **Every constant of a split block** is a former of the split, a
constructor of the split or a recursor of the split. -/
theorem blockSplit_mem : ∀ {block : List Lean.ConstantInfo} {cvTs cs rs},
    InLean.blockSplit block = some (cvTs, cs, rs) → ∀ ci ∈ block,
      (∃ v, ci = .inductInfo v ∧ v.toConstantVal ∈ cvTs) ∨
      (∃ v, ci = .ctorInfo v ∧ (v.toConstantVal, v.numParams, v.numFields) ∈ cs) ∨
      (∃ v, ci = .recInfo v ∧ (v.toConstantVal, majorIdxOf v, rulePrefixOf v, v.k, v.rules) ∈ rs)
  | .inductInfo v :: rest, cvTs, cs, rs, h => by
    simp only [InLean.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨q, h1, h2⟩ := h
    obtain ⟨q1, q2, q3⟩ := q
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    intro ci hci
    rcases List.mem_cons.1 hci with rfl | hci
    · exact .inl ⟨v, rfl, List.mem_cons_self⟩
    · rcases blockSplit_mem h1 ci hci with ⟨w, hw, hm⟩ | hr
      · exact .inl ⟨w, hw, List.mem_cons_of_mem _ hm⟩
      · exact .inr hr
  | [], cvTs, cs, rs, h | .recInfo _ :: _, cvTs, cs, rs, h | .ctorInfo _ :: _, cvTs, cs, rs, h
  | .axiomInfo _ :: _, cvTs, cs, rs, h | .defnInfo _ :: _, cvTs, cs, rs, h
  | .thmInfo _ :: _, cvTs, cs, rs, h | .opaqueInfo _ :: _, cvTs, cs, rs, h
  | .quotInfo _ :: _, cvTs, cs, rs, h => by
    unfold InLean.blockSplit at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨q, h1, rfl, rfl, rfl⟩ := h
    intro ci hci
    exact .inr (blockSplitCtors_mem h1 ci hci)

end InLeanProof
