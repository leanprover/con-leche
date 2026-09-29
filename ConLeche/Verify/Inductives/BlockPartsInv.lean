module

public import ConLeche.Kernel.Inductives.BlockParts

public section

/-!
# The k-ary block recogniser, inverted

`blockShape?` reads a block into a `BlockShape` at ANY number of
members and `blockParts?` adds the recursor records' structural pin
(`ConLeche/Kernel/Inductives/BlockParts.lean`).  The inversions here
read back: the `isProp` pin, the block's level parameters carried by
every member and every constructor, the reserved-name exclusions, the
parameter count, and the MEMBERS themselves: the type formers zipped with their index counts, their
GROUP of constructors and their recursor record, in block order.

What the recogniser does NOT pin (#220) is
everything the recursor RECORDS claim: their names, their level
parameters, their argument sums and their rules.  The recursor stage throws on them
(`targetRecPins`, `blockRecLpsOk`, `targetRulePins`), so a block
whose recursor record is a stub is REJECTED by its own type and
constructors rather than declined.
-/

namespace ConLeche

/-! ## The members' counts -/

/-- The member-counts loop yields one count per member. -/
theorem blockMemberCounts?_length {nPd k nC : Nat} {names : List Name}
    {rs : List (ConstantVal × Nat × Nat × List RecRule)} :
    ∀ {cvTs : List ConstantVal} {m : Nat} {nIdxs : List Nat},
      blockMemberCounts? nPd k nC names rs m cvTs = some nIdxs →
      nIdxs.length = cvTs.length
  | [], _, _, h => by
    simp only [blockMemberCounts?, Option.some.injEq] at h
    subst h; rfl
  | cvT :: ts, m, nIdxs, h => by
    rw [blockMemberCounts?] at h
    cases hc : blockCounts? nPd k nC rs.length cvT
        ((rs.find? fun q => recTargetOf names q.2.1 q.1.type == m).map
          fun q => (q.2.1, q.2.2.1)) with
    | none => rw [hc] at h; exact nomatch h
    | some c =>
    rw [hc] at h
    cases hm : blockMemberCounts? nPd k nC names rs (m + 1) ts with
    | none => rw [hm] at h; exact nomatch h
    | some ns =>
      rw [hm] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp [blockMemberCounts?_length hm]

/-! ## The grouping -/

/-- Every group is a sublist of the block's constructors: at ONE
member the group IS the list, at two or more it is the filter by
result head. -/
theorem mem_blockGroups {names lps : List Name} {nP k : Nat}
    {cs : List (ConstantVal × Nat)} {g : List (ConstantVal × Nat)}
    (hg : g ∈ blockGroups names lps nP k cs) {c : ConstantVal × Nat} (hc : c ∈ g) :
    c ∈ cs := by
  unfold blockGroups at hg
  split at hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg; exact hc
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
    exact (List.mem_filter.mp hc).1

/-- There is one group per member. -/
theorem blockGroups_length {names lps : List Name} {nP k : Nat}
    {cs : List (ConstantVal × Nat)} : (blockGroups names lps nP k cs).length = k := by
  unfold blockGroups
  split
  · next hk => rw [beq_iff_eq.mp hk]; rfl
  · simp

/-! ## The members list, as the recogniser builds it -/

/-- A member of the zipped members list carries one of the type
formers and one of the groups. -/
theorem blockMembers_mem {cvTs : List ConstantVal} {nIdxs : List Nat}
    {groups : List (List (ConstantVal × Nat))} {ms : MemberShape}
    (h : ms ∈ ((cvTs.zip nIdxs).zip groups).map
      (fun a => (⟨a.1.1, a.1.2, a.2⟩ : MemberShape))) :
    ms.cvT ∈ cvTs ∧ ms.ctors ∈ groups := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
  obtain ⟨⟨cvT, nIdx⟩, g⟩ := a
  obtain ⟨h1, h2⟩ := List.of_mem_zip ha
  obtain ⟨h3, -⟩ := List.of_mem_zip h1
  exact ⟨h3, h2⟩

/-- The zipped members list reads back its three ingredients when they
are as long as the member list. -/
theorem blockMembers_proj {cvTs : List ConstantVal} :
    ∀ {nIdxs : List Nat} {groups : List (List (ConstantVal × Nat))},
      nIdxs.length = cvTs.length → groups.length = cvTs.length →
      (((cvTs.zip nIdxs).zip groups).map
          (fun a => (⟨a.1.1, a.1.2, a.2⟩ : MemberShape))).map (·.cvT) = cvTs ∧
      (((cvTs.zip nIdxs).zip groups).map
          (fun a => (⟨a.1.1, a.1.2, a.2⟩ : MemberShape))).map (·.nIdx) = nIdxs ∧
      (((cvTs.zip nIdxs).zip groups).map
          (fun a => (⟨a.1.1, a.1.2, a.2⟩ : MemberShape))).map (·.ctors) = groups := by
  induction cvTs with
  | nil =>
    intro nIdxs groups h1 h2
    cases nIdxs <;> cases groups <;> simp_all
  | cons cvT ts ih =>
    intro nIdxs groups h1 h2
    cases nIdxs with
    | nil => simp at h1
    | cons n ns =>
    cases groups with
    | nil => simp at h2
    | cons g gs =>
    have h1' : ns.length = ts.length := by simpa using h1
    have h2' : gs.length = ts.length := by simpa using h2
    obtain ⟨e1, e2, e3⟩ := ih h1' h2'
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [List.zip_cons_cons, List.map_cons, e1, e2, e3]

/-! ## The recogniser -/

/-- **What `blockShape?` pins of the block's data** (`blockShape?_inv`).
The existential is the recogniser's
reading, verbatim: the split into type formers, constructors and recursor records, the
members' index counts, the members as the formers zipped with their
counts and their GROUP of constructors, and the RECURSORS as the
stream exports them, each with the member its MAJOR names
(`recTargetOf`).  The conjuncts before it are the consequences every
consumer reads: the parameter count, the `isProp` pin, the block's
level parameters on every member and every constructor, the
reserved-name exclusions, and the elimination level parameter, which is
fresh at the large eliminator and `.anonymous` at the small one. -/
abbrev BlockShapeOk (nPd : Nat) (block : List ConstantInfo) (p : BlockShape) : Prop :=
  p.nP = nPd ∧
  p.isProp = (Level.isEquiv p.resSort .zero == some true) ∧
  p.members ≠ [] ∧
  (∀ ms ∈ p.members, ms.cvT.levelParams = p.lps ∧
    reservedBasisNames.contains ms.cvT.name = false) ∧
  (∀ rc ∈ p.recs, reservedBasisNames.contains rc.cvR.name = false) ∧
  (∀ c ∈ p.allCtors, c.1.levelParams = p.lps ∧
    reservedBasisNames.contains c.1.name = false) ∧
  (p.large = true → p.lps.contains p.elim = false) ∧
  (p.large = false → p.elim = Name.anonymous) ∧
  ∃ (cvTs : List ConstantVal) (cs : List (ConstantVal × Nat × Nat))
    (rs : List (ConstantVal × Nat × Nat × List RecRule)) (nIdxs : List Nat),
    blockSplit block = some (cvTs, cs, rs) ∧
    cvTs.length = p.k ∧ rs.length = p.recs.length ∧ nIdxs.length = p.k ∧
    blockMemberCounts? nPd p.k cs.length p.memberNames rs 0 cvTs = some nIdxs ∧
    (∀ c ∈ cs, c.2.1 = p.nP) ∧
    p.members = ((cvTs.zip nIdxs).zip
        (blockGroups p.memberNames p.lps p.nP p.k
            (cs.map fun c => (c.1, c.2.2)))).map
      (fun a => ⟨a.1.1, a.1.2, a.2⟩) ∧
    p.recs = rs.map (fun r =>
      ⟨r.1, r.2.2.1, r.2.1, recTargetOf p.memberNames r.2.1 r.1.type,
        r.2.2.2.map RecRule.rhs⟩)

/-- The shared tail of `blockShape?_inv`: everything below the
eliminator reading, which the two branches differ in only by `elim`
and `large`. -/
private theorem blockShape?_inv_aux {nPd : Nat} {block : List ConstantInfo}
    {p : BlockShape} {cvT0 : ConstantVal} {cvTs' : List ConstantVal}
    {cs : List (ConstantVal × Nat × Nat)}
    {rs : List (ConstantVal × Nat × Nat × List RecRule)} {nIdxs : List Nat}
    (hsp : blockSplit block = some (cvT0 :: cvTs', cs, rs))
    (hmc : blockMemberCounts? nPd (cvT0 :: cvTs').length cs.length
      ((cvT0 :: cvTs').map (·.name)) rs 0 (cvT0 :: cvTs') = some nIdxs)
    (hresT : ∀ c ∈ cvT0 :: cvTs', reservedBasisNames.contains c.name = false)
    (hresR : ∀ r ∈ rs, reservedBasisNames.contains (Prod.fst r).name = false)
    (hlpsAll : ∀ c ∈ cvT0 :: cvTs', c.levelParams = cvT0.levelParams)
    (hcs : ∀ c ∈ cs, (c.2.1 = nPd ∧ c.1.levelParams = cvT0.levelParams) ∧
      reservedBasisNames.contains c.1.name = false)
    (hnP : p.nP = nPd)
    (hisProp : p.isProp = (Level.isEquiv p.resSort .zero == some true))
    (hlargeT : p.large = true → cvT0.levelParams.contains p.elim = false)
    (hlargeF : p.large = false → p.elim = Name.anonymous)
    (hmembers : p.members = (((cvT0 :: cvTs').zip nIdxs).zip
        (blockGroups ((cvT0 :: cvTs').map (·.name)) cvT0.levelParams nPd
            (cvT0 :: cvTs').length (cs.map fun c => (c.1, c.2.2)))).map
      (fun a => ⟨a.1.1, a.1.2, a.2⟩))
    (hrecs : p.recs = rs.map fun r =>
      ⟨r.1, r.2.2.1, r.2.1, recTargetOf ((cvT0 :: cvTs').map (·.name)) r.2.1 r.1.type,
        r.2.2.2.map RecRule.rhs⟩) :
    BlockShapeOk nPd block p := by
  have hlenN := blockMemberCounts?_length hmc
  obtain ⟨e1, e2, e3⟩ := blockMembers_proj (cvTs := cvT0 :: cvTs') (nIdxs := nIdxs)
    (groups := blockGroups ((cvT0 :: cvTs').map (·.name)) cvT0.levelParams nPd
      (cvT0 :: cvTs').length (cs.map fun c => (c.1, c.2.2)))
    hlenN blockGroups_length
  rw [← hmembers] at e1 e2 e3
  -- the block's data, read back off the members list
  have hk : p.k = (cvT0 :: cvTs').length := by
    have hl := congrArg List.length e1
    simp only [List.length_map] at hl
    rw [BlockShape.k]; exact hl
  have hhd : p.members.head?.map (fun ms => ms.cvT) = some cvT0 := by
    rw [← List.head?_map, e1]; rfl
  have hne : p.members ≠ [] := by
    intro hnil
    rw [hnil] at hhd
    exact nomatch hhd
  have hlpsP : p.lps = cvT0.levelParams := by
    unfold BlockShape.lps
    cases hm : p.members with
    | nil => rw [hm] at hhd; exact nomatch hhd
    | cons ms rest =>
      rw [hm] at hhd
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
      simp [hhd]
  have hnames : p.memberNames = (cvT0 :: cvTs').map (·.name) := by
    rw [BlockShape.memberNames, ← e1, List.map_map]
    rfl
  have hlenR : rs.length = p.recs.length := by rw [hrecs, List.length_map]
  refine ⟨hnP, hisProp, hne, ?_, ?_, ?_, ?_, hlargeF, cvT0 :: cvTs', cs, rs, nIdxs, hsp,
    hk.symm, hlenR, hlenN.trans hk.symm, ?_, ?_, ?_, ?_⟩
  · -- every member carries the block's level parameters and is not a basis name
    intro ms hms
    obtain ⟨hT, -⟩ := blockMembers_mem (hmembers ▸ hms)
    exact ⟨(hlpsAll _ hT).trans hlpsP.symm, hresT _ hT⟩
  · -- no recursor is a basis name either
    intro rc hrc
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (hrecs ▸ hrc)
    exact hresR r hr
  · -- every constructor carries them too
    intro c hc
    obtain ⟨g, hg, hcg⟩ := List.mem_flatten.mp hc
    rw [e3] at hg
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (mem_blockGroups hg hcg)
    exact ⟨((hcs c' hc').1.2).trans hlpsP.symm, (hcs c' hc').2⟩
  · intro hl; rw [hlpsP]; exact hlargeT hl
  · rw [hk, hnames]; exact hmc
  · intro c hc; rw [hnP]; exact (hcs c hc).1.1
  · rw [hnames, hlpsP, hnP, hk]; exact hmembers
  · rw [hnames]; exact hrecs

/-- **`blockShape?` pins the block's data** (`BlockShapeOk`). -/
theorem blockShape?_inv {nPd : Nat} {block : List ConstantInfo} {p : BlockShape}
    (h : blockShape? nPd block = some p) :
    BlockShapeOk nPd block p := by
  unfold blockShape? at h
  obtain ⟨cvTs, cs, rs, hsp⟩ :
      ∃ cvTs cs rs, blockSplit block = some (cvTs, cs, rs) := by
    cases hs : blockSplit block with
    | none => rw [hs] at h; exact nomatch h
    | some q => obtain ⟨a, b, c⟩ := q; exact ⟨a, b, c, rfl⟩
  rw [hsp] at h
  cases cvTs with
  | nil => exact nomatch h
  | cons cvT0 cvTs' =>
  cases rs with
  | nil => exact nomatch h
  | cons r0 rs' =>
  obtain ⟨cvR0, mI0, rP0, rules0⟩ := r0
  simp only at h
  cases hmc : blockMemberCounts? nPd (cvT0 :: cvTs').length cs.length
      ((cvT0 :: cvTs').map (·.name)) ((cvR0, mI0, rP0, rules0) :: rs') 0
      (cvT0 :: cvTs') with
  | none => rw [hmc] at h; exact nomatch h
  | some nIdxs =>
  rw [hmc] at h
  simp only at h
  split at h
  case isFalse => exact nomatch h
  case isTrue hif =>
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hif
  obtain ⟨⟨⟨hresT, hresR⟩, hlpsAll⟩, hcs⟩ := hif
  split at h
  · next elim helim =>
    have hp := Option.some.inj h
    refine blockShape?_inv_aux hsp hmc hresT hresR hlpsAll hcs ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← hp]
    · rw [← hp]
    · -- the large eliminator's level parameter is fresh
      rw [← hp]
      intro _
      revert helim
      generalize cvR0.levelParams = L
      cases L with
      | nil => intro hh; exact nomatch hh
      | cons e relps =>
        intro hh
        simp only at hh
        split at hh
        · next hfresh =>
          simp only [Option.some.injEq] at hh
          subst hh
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
            Bool.not_true] at hfresh
          exact hfresh.2
        · exact nomatch hh
    · rw [← hp]; intro hh; exact nomatch hh
    · rw [← hp]
    · rw [← hp]
  · next helim =>
    have hp := Option.some.inj h
    refine blockShape?_inv_aux hsp hmc hresT hresR hlpsAll hcs ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← hp]
    · rw [← hp]
    · rw [← hp]; intro hh; exact nomatch hh
    · rw [← hp]; intro _; rfl
    · rw [← hp]
    · rw [← hp]

/-- The recogniser is shape-only. -/
theorem blockParts?_inv {nPd : Nat} {block : List ConstantInfo} {p : BlockParts}
    (h : blockParts? nPd block = some p) :
    blockShape? nPd block = some p.toBlockShape := by
  unfold blockParts? at h
  split at h
  · next q hq =>
    obtain rfl := Option.some.inj h
    exact hq
  · exact nomatch h

end ConLeche
