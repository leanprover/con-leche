module

public import ConLeche.Kernel.Inductives.BlockParts
public import ConLeche.Verify.Inductives.FixParts

public section

/-!
# The uniform route at ONE member: the bridge to the one-member stages
(milestone M1)

The uniform installer is written at any number of members and the route
is gated at one (`blockRouteK1Only`, decision D6).  This file is the
bridge the gate buys: **at `k = 1` every uniform stage IS the
one-member stage**, through `BlockParts.toNative`.  The recogniser's
half is here (`blockParts?_toNative`); the install's half is
`ConLeche/Verify/Inductives/BlockOneInstall.lean`.

So the run relation, the P tier's `declNative` and every cached-mirror
agreement keep their one-member statements while the kernel's route is
the k-ary one — which is what makes each milestone of the uniform
overhaul a complete, proved checker.  When the gate goes (milestone
M6), these bridges go with it and the statements are restated at k.
-/

namespace ConLeche

/-! ## The split -/

theorem blockSplitRecs_nil {l : List ConstantInfo} (h : blockSplitRecs l = some []) :
    l = [] := by
  cases l with
  | nil => rfl
  | cons a l =>
    cases a with
    | recInfo cvR mI rP rules =>
      simp only [blockSplitRecs] at h
      cases hr : blockSplitRecs l with
      | none => rw [hr] at h; exact nomatch h
      | some rs => rw [hr] at h; exact nomatch h
    | _ => simp only [blockSplitRecs] at h; exact nomatch h

theorem blockSplitCtors_sumSplit :
    ∀ (l : List ConstantInfo) (cs : List (ConstantVal × Nat × Nat))
      (r : ConstantVal × Nat × Nat × List RecRule),
      blockSplitCtors l = some (cs, [r]) →
        sumSplit l = some (cs, r.1, r.2.1, r.2.2.1, r.2.2.2) := by
  intro l
  induction l with
  | nil =>
    intro cs r h
    simp only [blockSplitCtors, blockSplitRecs] at h
    exact nomatch h
  | cons a l ih =>
    cases a with
    | ctorInfo cvC nP nF =>
      intro cs r h
      simp only [blockSplitCtors] at h
      cases hb : blockSplitCtors l with
      | none => rw [hb] at h; exact nomatch h
      | some q =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, hq2⟩ := h
        have : q = (q.1, [r]) := by
          cases q with | mk q1 q2 => simp only at hq2; simp [hq2]
        rw [this] at hb
        simp only [sumSplit, ih q.1 r hb, Option.map_some]
    | recInfo cvR mI rP rules =>
      intro cs r h
      simp only [blockSplitCtors, blockSplitRecs] at h
      cases hr : blockSplitRecs l with
      | none => rw [hr] at h; exact nomatch h
      | some rs =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at h
        obtain ⟨rfl, hr1, hrs⟩ := h
        have hl : l = [] := blockSplitRecs_nil (by rw [hr, ← hrs])
        subst hl
        subst hr1
        rfl
    | _ =>
      intro cs r h
      simp only [blockSplitCtors, blockSplitRecs] at h
      exact nomatch h

private theorem optmap_pair_nil
    {q : Option (List (ConstantVal × Nat × Nat) × List (ConstantVal × Nat × Nat × List RecRule))}
    {cs : List (ConstantVal × Nat × Nat)} {rs : List (ConstantVal × Nat × Nat × List RecRule)}
    (h : (q.map fun z => (([] : List ConstantVal), z.1, z.2)) = some ([], cs, rs)) :
    q = some (cs, rs) := by
  cases q with
  | none => exact nomatch h
  | some z =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, h1, h2⟩ := h
    cases z; simp_all

private theorem optmap_pair_nil_ne
    {q : Option (List (ConstantVal × Nat × Nat) × List (ConstantVal × Nat × Nat × List RecRule))}
    {cvT : ConstantVal} {ts : List ConstantVal} {cs : List (ConstantVal × Nat × Nat)}
    {rs : List (ConstantVal × Nat × Nat × List RecRule)}
    (h : (q.map fun z => (([] : List ConstantVal), z.1, z.2)) = some (cvT :: ts, cs, rs)) :
    False := by
  cases q with
  | none => exact nomatch h
  | some z =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact nomatch h.1

theorem blockSplit_nil_inds :
    ∀ {l : List ConstantInfo} {cs : List (ConstantVal × Nat × Nat)}
      {rs : List (ConstantVal × Nat × Nat × List RecRule)},
      blockSplit l = some ([], cs, rs) → blockSplitCtors l = some (cs, rs) := by
  intro l cs rs h
  cases l with
  | nil => exact optmap_pair_nil (by simpa only [blockSplit] using h)
  | cons a l =>
    cases a with
    | indInfo cv caps =>
      simp only [blockSplit] at h
      cases hb : blockSplit l with
      | none => rw [hb] at h; exact nomatch h
      | some q =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        exact nomatch h.1
    | _ => exact optmap_pair_nil (by simpa only [blockSplit] using h)

/-- **The split at ONE member** is the one-member split: the head
former, then `sumSplit`. -/
theorem blockSplit_one {block : List ConstantInfo} {cvT : ConstantVal}
    {cs : List (ConstantVal × Nat × Nat)} {r : ConstantVal × Nat × Nat × List RecRule}
    (h : blockSplit block = some ([cvT], cs, [r])) :
    ∃ caps rest, block = .indInfo cvT caps :: rest ∧
      sumSplit rest = some (cs, r.1, r.2.1, r.2.2.1, r.2.2.2) := by
  cases block with
  | nil => simp only [blockSplit, blockSplitCtors, blockSplitRecs] at h; exact nomatch h
  | cons a rest =>
    cases a with
    | indInfo cv caps =>
      simp only [blockSplit] at h
      cases hb : blockSplit rest with
      | none => rw [hb] at h; exact nomatch h
      | some q =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at h
        obtain ⟨⟨rfl, hnil⟩, hq2⟩ := h
        refine ⟨caps, rest, rfl, blockSplitCtors_sumSplit rest cs r ?_⟩
        refine blockSplit_nil_inds (rs := [r]) ?_
        rw [hb]
        cases q with
        | mk q1 q2 => simp only at hnil hq2; simp [hnil, hq2]
    | _ =>
      simp only [blockSplit] at h
      exact absurd h optmap_pair_nil_ne

/-! ## The recogniser -/

/-- The member counts at ONE member are the one-member counts. -/
theorem blockCounts?_one (nPd : Nat) (cvT : ConstantVal)
    (cs : List (ConstantVal × Nat × Nat)) (mI rP : Nat) :
    blockCounts? nPd 1 cs.length cvT mI rP = nativeCounts? nPd cvT cs mI rP := rfl

/-- **The recogniser at ONE member is the one-member recogniser.** -/
theorem blockShape?_one {nPd : Nat} {block : List ConstantInfo} {cvT0 : ConstantVal}
    {cs : List (ConstantVal × Nat × Nat)} {rs : List (ConstantVal × Nat × Nat × List RecRule)}
    {q : BlockShape}
    (hsp : blockSplit block = some ([cvT0], cs, rs))
    (h : blockShape? nPd block = some q) :
    nativeShape? nPd block = some q.toInductive ∧
      ∃ r0 : ConstantVal × Nat × Nat × List RecRule, rs = [r0] ∧
        q.members = [⟨cvT0, q.toInductive.nIdx, cs.map fun c => (c.1, c.2.2),
          r0.1, r0.2.2.2.map RecRule.rhs⟩] := by
  unfold blockShape? at h
  rw [hsp] at h
  cases rs with
  | nil => simp only at h; exact nomatch h
  | cons r0 rs' =>
  cases rs' with
  | cons r1 rs'' =>
    cases hbc : blockCounts? nPd [cvT0].length cs.length cvT0 r0.2.1 r0.2.2.1 <;>
      simp only [blockMemberCounts?, hbc, Option.map_none] at h <;>
      exact nomatch h
  | nil =>
  obtain ⟨caps, rest, rfl, hsum⟩ := blockSplit_one hsp
  simp only [blockMemberCounts?, List.length_cons, List.length_nil,
    blockCounts?_one nPd cvT0 cs] at h
  cases hc : nativeCounts? nPd cvT0 cs r0.2.1 r0.2.2.1 with
  | none => rw [hc] at h; exact nomatch h
  | some cnt =>
  obtain ⟨nP, nIdx⟩ := cnt
  rw [hc] at h
  simp only [Option.map_some] at h
  simp only [nativeShape?, hsum]
  have hnP : nP = nPd := by
    unfold nativeCounts? at hc
    split at hc
    · split at hc
      · exact (congrArg Prod.fst (Option.some.inj hc)).symm
      · exact nomatch hc
    · split at hc
      · exact nomatch hc
      · split at hc
        · exact (congrArg Prod.fst (Option.some.inj hc)).symm
        · exact nomatch hc
  subst hnP
  rw [hc]
  simp only [List.all_cons, List.all_nil, Bool.and_true, beq_self_eq_true,
    blockGroups, Bool.and_assoc] at h ⊢
  split at h
  · rename_i hcnd
    rw [if_pos (by simpa [Bool.and_assoc] using hcnd)]
    cases hl : r0.1.levelParams with
    | nil =>
      simp only [hl] at h ⊢
      obtain rfl := Option.some.inj h; exact ⟨rfl, r0, rfl, rfl⟩
    | cons elim relps =>
      simp only [hl] at h ⊢
      by_cases hg : (relps == cvT0.levelParams && !cvT0.levelParams.contains elim) = true
      · rw [if_pos hg] at h ⊢; obtain rfl := Option.some.inj h; exact ⟨rfl, r0, rfl, rfl⟩
      · rw [if_neg hg] at h ⊢; obtain rfl := Option.some.inj h; exact ⟨rfl, r0, rfl, rfl⟩
  · exact nomatch h

/-- **The recursor pin at ONE member is the one-member pin.** -/
theorem blockRecPinOk_one {block : List ConstantInfo} {cvT0 : ConstantVal}
    {cs : List (ConstantVal × Nat × Nat)} {r0 : ConstantVal × Nat × Nat × List RecRule}
    {q : BlockShape} {nIdx : Nat}
    (hsp : blockSplit block = some ([cvT0], cs, [r0]))
    (hm : q.members = [⟨cvT0, nIdx, cs.map fun c => (c.1, c.2.2),
      r0.1, r0.2.2.2.map RecRule.rhs⟩]) :
    blockRecPinOk q block = nativeRecPinOk q.toInductive block := by
  obtain ⟨caps, rest, rfl, hsum⟩ := blockSplit_one hsp
  unfold blockRecPinOk nativeRecPinOk
  rw [hsp]
  simp only [hsum, BlockShape.k, BlockShape.allCtors, BlockShape.rulePrefix,
    BlockShape.numCtors, BlockShape.offs, BlockShape.toInductive, numCtorsOf, hm,
    List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.headD_cons, List.getElem?_cons_zero,
    List.map_map, Nat.add_zero, List.take, beq_self_eq_true, Bool.true_and,
    List.range_one, List.all_cons, List.all_nil, Bool.and_true, Nat.zero_add,
    Function.comp_def, beq_self_eq_true, Bool.true_and]
  rfl

/-- **THE RECOGNISER BRIDGE**: a block the uniform route takes is a
block the one-member route takes, at the one-member reading of the
record — and it has exactly one member (the gate). -/
theorem blockParts?_toNative {nPd : Nat} {block : List ConstantInfo} {p : BlockParts}
    (h : blockParts? nPd block = some p) :
    nativeParts? nPd block = some p.toNative ∧ ∃ ms, p.members = [ms] := by
  unfold blockParts? at h
  cases hsp : blockSplit block with
  | none => rw [hsp] at h; exact nomatch h
  | some z =>
  obtain ⟨cvTs, cs, rs⟩ := z
  rw [hsp] at h
  simp only at h
  by_cases hg : (blockRouteK1Only && cvTs.length != 1) = true
  · rw [if_pos hg] at h; exact nomatch h
  rw [if_neg hg] at h
  have hlen : cvTs.length = 1 := by
    simp only [blockRouteK1Only, Bool.true_and, bne_iff_ne, ne_eq] at hg
    simpa using hg
  obtain ⟨cvT0, rfl⟩ : ∃ c, cvTs = [c] := by
    match cvTs, hlen with
    | [c], _ => exact ⟨c, rfl⟩
  cases hsh : blockShape? nPd block with
  | none => rw [hsh] at h; exact nomatch h
  | some q =>
  rw [hsh] at h
  simp only [Option.map_some, Option.some.injEq] at h
  obtain ⟨hnat, r0, rfl, hm⟩ := blockShape?_one hsp hsh
  subst h
  refine ⟨?_, _, hm⟩
  unfold nativeParts?
  rw [hnat]
  simp only [Option.map_some, Option.some.injEq, BlockParts.toNative,
    List.headD_nil, List.map_nil, NativeParts.mk.injEq]
  exact ⟨trivial, trivial, (blockRecPinOk_one hsp hm).symm⟩

end ConLeche
