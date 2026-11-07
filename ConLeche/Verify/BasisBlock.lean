module

public import ConLeche.Verify.EnvPreds
public import ConLeche.Kernel.Install

public section

/-!
# What a pinned basis block's install stores

A block under a pinned block's names passes the reserved names' check (`basisNamesOk`) only if it is
the pin up to its level-parameter names (`pinListOk`), and it is installed like any other block
(`blockConstants`, `blockTables`).  That install stores the installed pins at the record's names
(`BasisKind.storedAt`: each former with the capabilities its block gives it, every recursor rule
firing `.plain`) and no projection table (`blockInstall_pinned`).

The comparison ignores a former's capabilities and so does the recogniser, so the block is read as
the pins at its names (`blockShape?_dropCaps`); the rest is the recogniser's computation at those
pins, at any level-parameter names.
-/

namespace ConLeche

/-- **What a pinned block's install stores**: each installed pin at the names its record
declares. -/
@[expose] def BasisKind.storedAt (kind : BasisKind) (block : List ConstantInfo) :
    List ConstantInfo :=
  List.zipWith (fun pin c => pin.atLps c.toConstantVal.levelParams) kind.installed block

/-! ## The recogniser reads no former's capabilities -/

/-- A constant with an inductive's capabilities dropped. -/
@[expose] def ConstantInfo.dropCaps : ConstantInfo → ConstantInfo
  | .indInfo cv _ => .indInfo cv {}
  | c => c

theorem blockSplitRecs_dropCaps :
    ∀ block : List ConstantInfo, blockSplitRecs (block.map (·.dropCaps)) = blockSplitRecs block
  | [] => rfl
  | .recInfo cvR mI rP isK rules :: rest => by
    show blockSplitRecs (.recInfo cvR mI rP isK rules :: rest.map (·.dropCaps)) = _
    simp only [blockSplitRecs]
    rw [blockSplitRecs_dropCaps rest]
  | .axiomInfo .. :: _ | .defnInfo .. :: _ | .thmInfo .. :: _ | .indInfo .. :: _
  | .ctorInfo .. :: _ => rfl

theorem blockSplitCtors_dropCaps :
    ∀ block : List ConstantInfo, blockSplitCtors (block.map (·.dropCaps)) = blockSplitCtors block
  | [] => rfl
  | .ctorInfo cv nP nF :: rest => by
    show blockSplitCtors (.ctorInfo cv nP nF :: rest.map (·.dropCaps)) = _
    simp only [blockSplitCtors]
    rw [blockSplitCtors_dropCaps rest]
  | .recInfo cvR mI rP isK rules :: rest => by
    show blockSplitCtors (.recInfo cvR mI rP isK rules :: rest.map (·.dropCaps)) = _
    simp only [blockSplitCtors, blockSplitRecs]
    rw [blockSplitRecs_dropCaps rest]
  | .axiomInfo .. :: _ | .defnInfo .. :: _ | .thmInfo .. :: _ | .indInfo .. :: _ => rfl

theorem blockSplit_dropCaps :
    ∀ block : List ConstantInfo, blockSplit (block.map (·.dropCaps)) = blockSplit block
  | [] => rfl
  | .indInfo cv caps :: rest => by
    show blockSplit (.indInfo cv {} :: rest.map (·.dropCaps)) = _
    simp only [blockSplit]
    rw [blockSplit_dropCaps rest]
  | .ctorInfo cv nP nF :: rest => by
    show blockSplit (.ctorInfo cv nP nF :: rest.map (·.dropCaps)) = _
    simp only [blockSplit, blockSplitCtors]
    rw [blockSplitCtors_dropCaps rest]
  | .recInfo cvR mI rP isK rules :: rest => by
    show blockSplit (.recInfo cvR mI rP isK rules :: rest.map (·.dropCaps)) = _
    simp only [blockSplit, blockSplitCtors, blockSplitRecs]
    rw [blockSplitRecs_dropCaps rest]
  | .axiomInfo .. :: _ | .defnInfo .. :: _ | .thmInfo .. :: _ => rfl

/-- **The recogniser reads no former's capabilities.** -/
theorem blockShape?_dropCaps (nP : Nat) (block : List ConstantInfo) :
    blockShape? nP (block.map (·.dropCaps)) = blockShape? nP block := by
  unfold blockShape?
  rw [blockSplit_dropCaps]

/-- **A record the comparison passes is its pin at its names**, up to an inductive's capabilities
(a pin carries none). -/
theorem pinCopyOk_dropCaps {c pin : ConstantInfo} (h : pinCopyOk c pin = true)
    (hpin : pin.dropCaps = pin) :
    c.dropCaps = pin.atLps c.toConstantVal.levelParams := by
  simp only [pinCopyOk, Bool.and_eq_true] at h
  obtain ⟨-, ha⟩ := h
  generalize c.toConstantVal.levelParams = ps at ha ⊢
  cases pin with
  | indInfo cvp capsp =>
    have hc : capsp = {} := by
      simp only [ConstantInfo.dropCaps, ConstantInfo.indInfo.injEq, true_and] at hpin
      exact hpin.symm
    subst hc
    cases c with
    | indInfo cv caps =>
      simp only [ConstantInfo.atLps, pinAgrees] at ha
      rw [ConstantVal.eq_of_beqP ha]
      rfl
    | _ => simp [ConstantInfo.atLps, pinAgrees, ConstantInfo.beqP] at ha
  | _ =>
    cases c <;> simp only [ConstantInfo.atLps, pinAgrees] at ha <;>
      first
        | exact ConstantInfo.eq_of_beqP ha
        | simp [ConstantInfo.beqP] at ha

/-- The whole block, position by position. -/
theorem listBeqBy_pinCopyOk_dropCaps :
    ∀ {block pins : List ConstantInfo}, listBeqBy pinCopyOk block pins = true →
      (∀ pin ∈ pins, pin.dropCaps = pin) →
      block.map (·.dropCaps) =
        List.zipWith (fun pin c => pin.atLps c.toConstantVal.levelParams) pins block
  | [], [], _, _ => rfl
  | c :: cs, pin :: pins, h, hp => by
    simp only [listBeqBy, Bool.and_eq_true] at h
    simp only [List.map_cons, List.zipWith_cons_cons]
    rw [pinCopyOk_dropCaps h.1 (hp pin List.mem_cons_self),
      listBeqBy_pinCopyOk_dropCaps h.2 fun x hx => hp x (List.mem_cons_of_mem _ hx)]
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h

/-! ## The four pinned blocks -/

theorem emptyBlock_install {nP : Nat} {block : List ConstantInfo} {p : BlockShape}
    (hok : listBeqBy pinCopyOk block emptyBasis = true) (hp : blockShape? nP block = some p) :
    blockConstants p = BasisKind.emptyK.storedAt block ∧ blockTables p p.members = [] := by
  have hd := listBeqBy_pinCopyOk_dropCaps hok fun pin hpin => by
    simp only [emptyBasis, List.mem_cons, List.not_mem_nil, or_false] at hpin
    rcases hpin with rfl | rfl <;> rfl
  rw [← blockShape?_dropCaps, hd] at hp
  match block, hok with
  | [b1, b2], hok =>
    simp only [emptyBasis, listBeqBy, pinCopyOk, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨-, hl1⟩, -⟩, ⟨-, hl2⟩, -⟩ := hok
    simp only [BasisKind.storedAt, BasisKind.installed, List.zipWith_cons_cons, List.zipWith_nil_left]
    simp only [emptyBasis, List.zipWith_cons_cons, List.zipWith_nil_left] at hp
    generalize b1.toConstantVal.levelParams = ps1 at hl1 hp ⊢
    generalize b2.toConstantVal.levelParams = ps2 at hl2 hp ⊢
    simp [emptyA, ConstantInfo.toConstantVal] at hl1
    subst hl1
    simp [emptyRecA, ConstantInfo.toConstantVal] at hl2
    match ps2, hl2 with
    | [q], _ =>
    simp [blockShape?, blockSplit, blockSplitCtors, blockSplitRecs, emptyA, emptyRecA, ConstantInfo.atLps,
      ConstantVal.atLps, Expr.instantiateLevelParams, blockMemberCounts?, blockCounts?, BasisDSL.type1,
      BasisDSL.pi, BasisDSL.cnst, BasisDSL.srt, BasisDSL.bv, BasisDSL.u, Level.subst, Level.subst.go,
      Expr.piBinders, recTargetOf, Expr.stripPis, Expr.getAppFn, blockGroups] at hp
    by_cases h0 : nP = 0
    · subst h0
      simp at hp
      subst hp
      refine ⟨?_, rfl⟩
      simp [blockConstants, blockFormers, blockCtors, blockRecs, blockCapsAt, blockIsRec, recFire,
        BlockShape.allCtors, BlockShape.memberNames, BlockShape.k, emptyI, emptyA, emptyRecA,
        ConstantInfo.atLps, ConstantVal.atLps, ConstantInfo.toConstantVal, Expr.instantiateLevelParams,
        BasisDSL.type1, BasisDSL.pi, BasisDSL.cnst, BasisDSL.srt, BasisDSL.bv, BasisDSL.u, Level.subst,
        Level.subst.go]
    · simp [h0] at hp
  | [], h | [_], h | _ :: _ :: _ :: _, h => simp [emptyBasis, listBeqBy] at h

theorem falseBlock_install {nP : Nat} {block : List ConstantInfo} {p : BlockShape}
    (hok : listBeqBy pinCopyOk block falseBasis = true) (hp : blockShape? nP block = some p) :
    blockConstants p = BasisKind.falseK.storedAt block ∧ blockTables p p.members = [] := by
  have hd := listBeqBy_pinCopyOk_dropCaps hok fun pin hpin => by
    simp only [falseBasis, List.mem_cons, List.not_mem_nil, or_false] at hpin
    rcases hpin with rfl | rfl <;> rfl
  rw [← blockShape?_dropCaps, hd] at hp
  match block, hok with
  | [b1, b2], hok =>
    simp only [falseBasis, listBeqBy, pinCopyOk, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨-, hl1⟩, -⟩, ⟨-, hl2⟩, -⟩ := hok
    simp only [BasisKind.storedAt, BasisKind.installed, List.zipWith_cons_cons, List.zipWith_nil_left]
    simp only [falseBasis, List.zipWith_cons_cons, List.zipWith_nil_left] at hp
    generalize b1.toConstantVal.levelParams = ps1 at hl1 hp ⊢
    generalize b2.toConstantVal.levelParams = ps2 at hl2 hp ⊢
    simp [falseA, ConstantInfo.toConstantVal] at hl1
    subst hl1
    simp [falseRecA, ConstantInfo.toConstantVal] at hl2
    match ps2, hl2 with
    | [q], _ =>
    simp [blockShape?, blockSplit, blockSplitCtors, blockSplitRecs, falseA, falseRecA, ConstantInfo.atLps,
      ConstantVal.atLps, Expr.instantiateLevelParams, blockMemberCounts?, blockCounts?, BasisDSL.prop,
      BasisDSL.pi, BasisDSL.cnst, BasisDSL.srt, BasisDSL.bv, BasisDSL.u, Level.subst, Level.subst.go,
      Expr.piBinders, recTargetOf, Expr.stripPis, Expr.getAppFn, blockGroups] at hp
    by_cases h0 : nP = 0
    · subst h0
      simp at hp
      subst hp
      refine ⟨?_, rfl⟩
      simp [blockConstants, blockFormers, blockCtors, blockRecs, blockCapsAt, blockIsRec, recFire,
        BlockShape.allCtors, BlockShape.memberNames, BlockShape.k, falseI, falseA, falseRecA,
        ConstantInfo.atLps, ConstantVal.atLps, ConstantInfo.toConstantVal, Expr.instantiateLevelParams,
        BasisDSL.prop, BasisDSL.pi, BasisDSL.cnst, BasisDSL.srt, BasisDSL.bv, BasisDSL.u, Level.subst,
        Level.subst.go]
    · simp [h0] at hp
  | [], h | [_], h | _ :: _ :: _ :: _, h => simp [falseBasis, listBeqBy] at h

theorem eqBlock_install {nP : Nat} {block : List ConstantInfo} {p : BlockShape}
    (hok : listBeqBy pinCopyOk block eqBasis = true) (hp : blockShape? nP block = some p) :
    blockConstants p = BasisKind.eqK.storedAt block ∧ blockTables p p.members = [] := by
  have hd := listBeqBy_pinCopyOk_dropCaps hok fun pin hpin => by
    simp only [eqBasis, List.mem_cons, List.not_mem_nil, or_false] at hpin
    rcases hpin with rfl | rfl | rfl <;> rfl
  rw [← blockShape?_dropCaps, hd] at hp
  match block, hok with
  | [b1, b2, b3], hok =>
    simp only [eqBasis, listBeqBy, pinCopyOk, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨-, hl1⟩, -⟩, ⟨⟨-, hl2⟩, -⟩, ⟨-, hl3⟩, -⟩ := hok
    simp only [BasisKind.storedAt, BasisKind.installed, List.zipWith_cons_cons, List.zipWith_nil_left]
    simp only [eqBasis, List.zipWith_cons_cons, List.zipWith_nil_left] at hp
    generalize b1.toConstantVal.levelParams = ps1 at hl1 hp ⊢
    generalize b2.toConstantVal.levelParams = ps2 at hl2 hp ⊢
    generalize b3.toConstantVal.levelParams = ps3 at hl3 hp ⊢
    simp [eqA, ConstantInfo.toConstantVal] at hl1
    simp [eqReflA, ConstantInfo.toConstantVal] at hl2
    simp [eqRecA, ConstantInfo.toConstantVal] at hl3
    match ps1, hl1, ps2, hl2, ps3, hl3 with
    | [a], _, [b], _, [c, d], _ =>
    simp [blockShape?, blockSplit, blockSplitCtors, blockSplitRecs, eqA, eqReflA, eqRecA, ConstantInfo.atLps,
      ConstantVal.atLps, Expr.instantiateLevelParams, blockMemberCounts?, blockCounts?, BasisDSL.prop,
      BasisDSL.pi, BasisDSL.piI, BasisDSL.cnst, BasisDSL.srt, BasisDSL.bv, BasisDSL.u, BasisDSL.u1,
      BasisDSL.ap2, BasisDSL.ap3, BasisDSL.rule, BasisDSL.lm, BasisDSL.lmI, eqRecMotive, Level.subst,
      Level.subst.go, Expr.piBinders, recTargetOf, Expr.stripPis, Expr.getAppFn, blockGroups,
      show BasisDSL.u1N ≠ BasisDSL.uN by decide] at hp
    by_cases h0 : nP = 2
    · subst h0
      by_cases hb : b = a
      · subst hb
        simp at hp
        split at hp <;>
        · simp only [Option.some.injEq] at hp
          subst hp
          refine ⟨?_, rfl⟩
          simp [blockConstants, blockFormers, blockCtors, blockRecs, blockCapsAt, blockIsRec, recFire,
            BlockShape.allCtors, BlockShape.memberNames, BlockShape.k, eqI, eqA, eqReflA, eqRecA,
            ConstantInfo.atLps, ConstantVal.atLps, ConstantInfo.toConstantVal,
            Expr.instantiateLevelParams, BasisDSL.prop, BasisDSL.pi, BasisDSL.piI, BasisDSL.cnst,
            BasisDSL.srt, BasisDSL.bv, BasisDSL.u, BasisDSL.u1, BasisDSL.ap2, BasisDSL.ap3,
            BasisDSL.rule, BasisDSL.lm, BasisDSL.lmI, eqRecMotive, Level.subst, Level.subst.go,
            RecRuleFire.atLps, show BasisDSL.u1N ≠ BasisDSL.uN by decide]
      · exfalso
        revert hp
        simp [hb]
    · exfalso
      revert hp
      simp [show ¬2 = nP from fun h => h0 h.symm]
      split <;> simp
  | [], h | [_], h | [_, _], h | _ :: _ :: _ :: _ :: _, h => simp [eqBasis, listBeqBy] at h

theorem natBlock_install {nP : Nat} {block : List ConstantInfo} {p : BlockShape}
    (hok : listBeqBy pinCopyOk block natBasis = true) (hp : blockShape? nP block = some p) :
    blockConstants p = BasisKind.natK.storedAt block ∧ blockTables p p.members = [] := by
  have hd := listBeqBy_pinCopyOk_dropCaps hok fun pin hpin => by
    simp only [natBasis, List.mem_cons, List.not_mem_nil, or_false] at hpin
    rcases hpin with rfl | rfl | rfl | rfl <;> rfl
  rw [← blockShape?_dropCaps, hd] at hp
  match block, hok with
  | [b1, b2, b3, b4], hok =>
    simp only [natBasis, listBeqBy, pinCopyOk, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨-, hl1⟩, -⟩, ⟨⟨-, hl2⟩, -⟩, ⟨⟨-, hl3⟩, -⟩, ⟨-, hl4⟩, -⟩ := hok
    simp only [BasisKind.storedAt, BasisKind.installed, List.zipWith_cons_cons, List.zipWith_nil_left]
    simp only [natBasis, List.zipWith_cons_cons, List.zipWith_nil_left] at hp
    generalize b1.toConstantVal.levelParams = ps1 at hl1 hp ⊢
    generalize b2.toConstantVal.levelParams = ps2 at hl2 hp ⊢
    generalize b3.toConstantVal.levelParams = ps3 at hl3 hp ⊢
    generalize b4.toConstantVal.levelParams = ps4 at hl4 hp ⊢
    simp [natA, ConstantInfo.toConstantVal] at hl1
    simp [natZeroA, ConstantInfo.toConstantVal] at hl2
    simp [natSuccA, ConstantInfo.toConstantVal] at hl3
    simp [natRecA, ConstantInfo.toConstantVal] at hl4
    subst hl1 hl2 hl3
    match ps4, hl4 with
    | [q], _ =>
    simp [blockShape?, blockSplit, blockSplitCtors, blockSplitRecs, natA, natZeroA, natSuccA, natRecA,
      ConstantInfo.atLps, ConstantVal.atLps, Expr.instantiateLevelParams, blockMemberCounts?,
      blockCounts?, BasisDSL.type1, BasisDSL.pi, BasisDSL.piI, BasisDSL.cnst, BasisDSL.srt, BasisDSL.bv,
      BasisDSL.u, BasisDSL.ap2, BasisDSL.ap4, BasisDSL.rule, BasisDSL.lm, natT, natRecMotive, natRecSucc,
      Level.subst, Level.subst.go, Expr.piBinders, recTargetOf, Expr.stripPis, Expr.getAppFn,
      blockGroups] at hp
    by_cases h0 : nP = 0
    · subst h0
      simp at hp
      subst hp
      refine ⟨?_, rfl⟩
      simp [blockConstants, blockFormers, blockCtors, blockRecs, blockCapsAt, blockIsRec, recFire,
        BlockShape.allCtors, BlockShape.memberNames, BlockShape.k, natI, natA, natZeroA, natSuccA,
        natRecA, ConstantInfo.atLps, ConstantVal.atLps, ConstantInfo.toConstantVal,
        Expr.instantiateLevelParams, BasisDSL.type1, BasisDSL.pi, BasisDSL.piI, BasisDSL.cnst,
        BasisDSL.srt, BasisDSL.bv, BasisDSL.u, BasisDSL.ap2, BasisDSL.ap4, BasisDSL.rule, BasisDSL.lm,
        natT, natRecMotive, natRecSucc, Level.subst, Level.subst.go, RecRuleFire.atLps,
        Expr.piDomsMentionAny, Expr.mentionsAnyConst]
    · simp [h0] at hp
  | [], h | [_], h | [_, _], h | [_, _, _], h | _ :: _ :: _ :: _ :: _ :: _, h =>
    simp [natBasis, listBeqBy] at h

/-- **A pinned block's install**: the installed pins at the record's names, and no projection
table. -/
theorem blockInstall_pinned {nP : Nat} {block : List ConstantInfo} {kind : BasisKind}
    {p : BlockShape} (hk : basisNameHit block = some kind) (hok : pinListOk block kind.decls = true)
    (hp : blockShape? nP block = some p) :
    blockConstants p = kind.storedAt block ∧ blockTables p p.members = [] := by
  simp only [pinListOk, Bool.and_eq_true] at hok
  cases kind with
  | eqK => exact eqBlock_install hok.1 hp
  | natK => exact natBlock_install hok.1 hp
  | emptyK => exact emptyBlock_install hok.1 hp
  | falseK => exact falseBlock_install hok.1 hp
  | quotK =>
    have hm := List.mem_of_find?_eq_some hk
    simp at hm

end ConLeche
