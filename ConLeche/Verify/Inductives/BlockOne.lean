module

public import ConLeche.Kernel.Inductives.BlockParts

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

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

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

/-! ## The install's per-member sums, while the recursor stage is gated -/

/-- **While `blockRecCheckOn` is down the install's per-member rule
prefix IS the generated block-wide one.**  The gate's whole purpose is
that the shipped tree behaves as the generate-and-compare stage does
(`ConLeche/Kernel/Inductives/BlockParts.lean`'s `rulePrefixAt`), and
that is what keeps every one-member bridge an EQUALITY while the
motive-free check reads the sums off the recursor record.  **This
theorem and its companion go with the gate at the flip.** -/
@[simp] theorem rulePrefixAt_gated (p : BlockShape) (m : Nat) :
    p.rulePrefixAt m = p.rulePrefix := rfl

/-- `rulePrefixAt_gated`'s companion at the major-premise index. -/
@[simp] theorem majorIdxAt_gated (p : BlockShape) (m : Nat) :
    p.majorIdxAt m = p.majorIdx m := rfl

/-! ## The recogniser -/

/-- **`recTgtAt` while the recursor stage's gate is down**: the route
takes one member with one recursor, so a recursor's position IS its
member's.  Goes with the gate. -/
@[simp] theorem recTgtAt_gated (p : BlockShape) (r : Nat) : p.recTgtAt r = r := rfl

/-- The member counts at ONE member, at the sums of the recursor the
loop found. -/
theorem blockCounts?_one (nPd : Nat) (cvT : ConstantVal)
    (cs : List (ConstantVal × Nat × Nat)) (mI rP : Nat) :
    blockCounts? nPd 1 cs.length cvT (some (mI, rP)) = nativeCounts? nPd cvT cs mI rP := rfl

/-- The member counts at ONE member when the loop found NO recursor
for it: the answer is the former's telescope's, which is the one-member
reading at ANY sums (the sums are read only at a def-headed former,
where the absence of a recursor is a `none`). -/
theorem blockCounts?_one_none {nPd : Nat} {cvT : ConstantVal}
    {cs : List (ConstantVal × Nat × Nat)} {c : Nat × Nat} (mI rP : Nat)
    (h : blockCounts? nPd 1 cs.length cvT none = some c) :
    nativeCounts? nPd cvT cs mI rP = some c := by
  revert h
  unfold blockCounts? nativeCounts?
  cases hb : cvT.type.piBinders with
  | mk bs body =>
    cases body <;> intro h <;> first
      | exact h
      | exact nomatch h

/-- **The recogniser at ONE member is the one-member recogniser.**
The recursor list is the stream's own, with the member its MAJOR names
read off its type (`recTargetOf`). -/
theorem blockShape?_one {nPd : Nat} {block : List ConstantInfo} {cvT0 : ConstantVal}
    {cs : List (ConstantVal × Nat × Nat)} {r0 : ConstantVal × Nat × Nat × List RecRule}
    {q : BlockShape}
    (hsp : blockSplit block = some ([cvT0], cs, [r0]))
    (h : blockShape? nPd block = some q) :
    nativeShape? nPd block = some q.toInductive ∧
      q.members = [⟨cvT0, q.toInductive.nIdx, cs.map fun c => (c.1, c.2.2)⟩] ∧
      q.recs = [⟨r0.1, r0.2.2.1, r0.2.1,
        recTargetOf [cvT0.name] r0.2.1 r0.1.type, r0.2.2.2.map RecRule.rhs⟩] := by
  unfold blockShape? at h
  rw [hsp] at h
  obtain ⟨caps, rest, rfl, hsum⟩ := blockSplit_one hsp
  simp only [blockMemberCounts?, List.length_cons, List.length_nil, List.map_cons,
    List.map_nil, Nat.zero_add] at h
  cases hc : blockCounts? nPd 1 cs.length cvT0
      ((([r0].find? fun z => recTargetOf [cvT0.name] z.2.1 z.1.type == 0).map
        fun z => (z.2.1, z.2.2.1))) with
  | none => rw [hc] at h; exact nomatch h
  | some cnt =>
  obtain ⟨nP, nIdx⟩ := cnt
  rw [hc] at h
  simp only [Option.map_some] at h
  simp only [nativeShape?, hsum]
  -- the one-member counts, at the sums the loop read or without them
  have hnat : nativeCounts? nPd cvT0 cs r0.2.1 r0.2.2.1 = some (nP, nIdx) := by
    revert hc
    simp only [List.find?, List.map]
    cases hf : (recTargetOf [cvT0.name] r0.2.1 r0.1.type == 0) with
    | true =>
      simp only [Option.map_some]
      intro hc
      rw [← blockCounts?_one nPd cvT0 cs r0.2.1 r0.2.2.1]
      exact hc
    | false =>
      simp only [Option.map_none]
      intro hc
      exact blockCounts?_one_none r0.2.1 r0.2.2.1 hc
  have hnP : nP = nPd := by
    unfold nativeCounts? at hnat
    split at hnat
    · split at hnat
      · exact (congrArg Prod.fst (Option.some.inj hnat)).symm
      · exact nomatch hnat
    · split at hnat
      · exact nomatch hnat
      · split at hnat
        · exact (congrArg Prod.fst (Option.some.inj hnat)).symm
        · exact nomatch hnat
  subst hnP
  rw [hnat]
  simp only [List.all_cons, List.all_nil, Bool.and_true, beq_self_eq_true,
    blockGroups, Bool.and_assoc] at h ⊢
  split at h
  · rename_i hcnd
    rw [if_pos (by simpa [Bool.and_assoc] using hcnd)]
    cases hl : r0.1.levelParams with
    | nil =>
      simp only [hl] at h ⊢
      obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, rfl⟩
    | cons elim relps =>
      simp only [hl] at h ⊢
      by_cases hg : (relps == cvT0.levelParams && !cvT0.levelParams.contains elim) = true
      · rw [if_pos hg] at h ⊢; obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, rfl⟩
      · rw [if_neg hg] at h ⊢; obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, rfl⟩
  · exact nomatch h

/-- **The recursor pin at ONE member is the one-member pin** — the
record's own pin (rule completeness) together with the two argument
SUMS, which the ruling of 2026-09-21 moved out of the record's pin and
into this, the generate-and-compare arm (`BlockParts.toNative` adds
them). -/
theorem blockRecPinOk_one {block : List ConstantInfo} {cvT0 : ConstantVal}
    {cs : List (ConstantVal × Nat × Nat)} {r0 : ConstantVal × Nat × Nat × List RecRule}
    {q : BlockShape} {nIdx : Nat} {tgt : Nat}
    (hsp : blockSplit block = some ([cvT0], cs, [r0]))
    (hm : q.members = [⟨cvT0, nIdx, cs.map fun c => (c.1, c.2.2)⟩])
    (hr : q.recs = [⟨r0.1, r0.2.2.1, r0.2.1, tgt, r0.2.2.2.map RecRule.rhs⟩]) :
    (q.recSumsOk && blockRecPinOk q block) = nativeRecPinOk q.toInductive block := by
  obtain ⟨caps, rest, rfl, hsum⟩ := blockSplit_one hsp
  unfold blockRecPinOk nativeRecPinOk BlockShape.recSumsOk
  rw [hsp]
  simp only [hsum, BlockShape.k, BlockShape.allCtors, BlockShape.rulePrefix,
    BlockShape.numCtors, BlockShape.offs, BlockShape.toInductive, numCtorsOf, hm, hr,
    recTgtAt_gated,
    List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.headD_cons, List.getElem?_cons_zero,
    List.map_map, Nat.add_zero, List.take, beq_self_eq_true, Bool.true_and,
    List.range_one, List.all_cons, List.all_nil, Bool.and_true, Nat.zero_add,
    Function.comp_def, List.getD_cons_zero, Bool.and_assoc]
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
  by_cases hg : (blockRouteK1Only && (cvTs.length != 1 || rs.length != 1)) = true
  · rw [if_pos hg] at h; exact nomatch h
  rw [if_neg hg] at h
  simp only [blockRouteK1Only, Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq,
    not_or, Decidable.not_not] at hg
  obtain ⟨cvT0, rfl⟩ : ∃ c, cvTs = [c] := by
    match cvTs, hg.1 with
    | [c], _ => exact ⟨c, rfl⟩
  obtain ⟨r0, rfl⟩ : ∃ r, rs = [r] := by
    match rs, hg.2 with
    | [r], _ => exact ⟨r, rfl⟩
  cases hsh : blockShape? nPd block with
  | none => rw [hsh] at h; exact nomatch h
  | some q =>
  rw [hsh] at h
  simp only at h
  obtain ⟨hnat, hm, hr⟩ := blockShape?_one hsp hsh
  by_cases hn : (q.recs.any fun rc => recMajorForeign q.memberNames rc.mI rc.cvR.type) = true
  · rw [if_pos hn] at h; exact nomatch h
  rw [if_neg hn] at h
  by_cases hk : (blockRouteK1Only && (q.k != 1 || q.recs.length != 1)) = true
  · rw [if_pos hk] at h; exact nomatch h
  rw [if_neg hk] at h
  obtain rfl := Option.some.inj h
  refine ⟨?_, _, hm⟩
  unfold nativeParts?
  rw [hnat]
  simp only [Option.map_some, Option.some.injEq, BlockParts.toNative,
    List.headD_nil, List.map_nil, NativeParts.mk.injEq]
  exact ⟨trivial, trivial, (blockRecPinOk_one hsp hm hr).symm⟩

end ConLeche
