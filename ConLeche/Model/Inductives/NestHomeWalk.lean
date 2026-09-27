module

public import ConLeche.Model.Inductives.NestHomeReach
public import ConLeche.Model.Cover

public section

/-!
# The walk's facts the home table reads, at a nested stage (PRIMREC / NESTHOME)

`HomeWalk` (`NestHomeReach.lean`) at the positivity derivation's node
list (`nestedRecCtx_nodes`): its nodes and kids, the member
constructors' derivations (`MemberForests`), and — the one fact about the
environment — a node's group whose member has no group-mates is that
member alone (`frame_grp_singleton`): a frame's group is its head's
recorded block, and the recorded blocks of the environment are
consistent (`LfpCover.all`: every recorded member's block is its
datum's names), so a member of another container's block has that
container as a group-mate.
-/

namespace ConLeche.Model

open ConLeche

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **A frame's group whose member has no group-mates is that member
alone** (see the module docstring). -/
theorem frame_grp_singleton {env envI : Env} {mk : EnvModelM V μ envI} {ex : List Name}
    (hcov : LfpCover mk ex) {ops : CheckerOps CheckM} {ctx : NestCtx}
    (hfind : ctx.find? = envI.find?) (hex : ctx.names = ex)
    {prog : List NestHole} {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    {ts : List PosTree} (hfr : PosD ops env ctx (.frame prog us ds grp) ts)
    {I : Name} (hI : I ∈ grp.map (·.1)) (hm : (nestFrameMates ctx I).isEmpty = true) :
    grp.map (·.1) = [I] := by
  cases hfr with
  | frame hne hhd hhdC hnd hinst hblk hgrp hctors hkty hwalk =>
    generalize hH : (grp.headD default).1 = H at *
    rw [hgrp] at hI ⊢
    rcases List.mem_cons.mp hI with rfl | hIm
    · simp only [List.isEmpty_iff] at hm
      rw [hm]
    · exfalso
      -- `I` is a group-mate of the head: the head's recorded block holds it
      simp only [nestFrameMates, List.mem_filter, bne_iff_ne, ne_eq] at hIm
      obtain ⟨hIb, hIH⟩ := hIm
      have hIb' : I ∈ nestBlockOf ctx H := List.mem_eraseDups.mp hIb
      unfold nestBlockOf at hIb'
      obtain ⟨L, hL⟩ := hhdC
      unfold nestContainer at hL
      rw [hfind] at hIb' hL
      split at hL
      · rename_i cvH capsH hfH
        rw [hfH] at hIb'
        simp only at hIb'
        -- the head's datum
        have hHnm : H ∉ ex := by
          rw [← hex]; intro h
          have := hhd.1; rw [List.contains_iff_mem.mpr h] at this; exact nomatch this
        obtain ⟨D, hD, mm, hmm, hmem⟩ := hcov.cover H cvH capsH hfH hHnm hhd.2
        have hallH := hcov.all D hD mm hmm cvH capsH (by rw [hmem]; exact hfH)
        rw [hallH] at hIb'
        obtain ⟨mm', hmm', hI'⟩ := List.getElem_of_mem hIb'
        have hmk : D.member mm' = I := by
          simp only [LfpDatum.member, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmm',
            Option.getD_some, hI']
        have hmm'k : mm' < D.k := by rw [← hcov.len D hD]; exact hmm'
        obtain ⟨cvI, capsI, hfI⟩ := LfpCover.member_find hD hmm'k
        have hallI := hcov.all D hD mm' hmm'k cvI capsI hfI
        rw [hmk] at hfI
        -- the head is a group-mate of `I`
        have hHmem : H ∈ D.names := by
          have hl : mm < D.names.length := by rw [hcov.len D hD]; exact hmm
          rw [← hmem]
          simp only [LfpDatum.member, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl,
            Option.getD_some]
          exact List.getElem_mem hl
        have hHin : H ∈ nestFrameMates ctx I := by
          simp only [nestFrameMates, nestBlockOf, hfind, hfI, hallI, List.mem_filter,
            bne_iff_ne, ne_eq]
          exact ⟨List.mem_eraseDups.mpr hHmem, fun h => hIH h.symm⟩
        simp only [List.isEmpty_iff] at hm
        rw [hm] at hHin
        exact nomatch hHin
      · exact nomatch hL

/-- **The walk's facts the table reads, at the derivation's node list.** -/
theorem homeWalk_of {F : Nat} {envI : Env} {pp : BlockParts}
    {ctorsAsR : List (List (ConstantVal × Nat))} {nfsR : List (List Expr)} {fvsP : List Expr}
    {ns : List PosTree} {mk : EnvModelM V μ envI}
    (hmkC : LfpCover mk pp.toBlockShape.memberNames)
    (hok : ∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t)
    (hkids : ∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns)
    {holes : List Expr}
    (hmemF : ∀ (m : Nat) (cs : List (ConstantVal × Nat)), ctorsAsR[m]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest ks ts,
        instPisWith fvsP (nestAbstract (pp.nestCtx fvsP envI.find? envI.consts) holes cA.1.type)
          = some crest ∧
        ConLeche.MemberCtorD (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts)
          cA.2 crest ks ((nfsR.getD m []).getD j default) ts ∧
        (∃ ty, ConLeche.inferTypeCore .verified envI F
          ((pp.nestCtx fvsP envI.find? envI.consts).hiAt 0) crest = .ok ty) ∧
        ∀ u ∈ PosTree.forest ts, u ∈ ns) :
    HomeWalk F envI (pp.nestCtx fvsP envI.find? envI.consts) holes ns ctorsAsR where
  hok := hok
  hkids := hkids
  hmem := by
    intro t _ cA hcA crest hcr
    rw [List.getD_eq_getElem?_getD] at hcA
    cases hcs : ctorsAsR[t]? with
    | none => rw [hcs] at hcA; exact nomatch hcA
    | some cs =>
      rw [hcs, Option.getD_some] at hcA
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcA
      obtain ⟨crest', ks, ts, hcr', hd, -, hts⟩ :=
        hmemF t cs hcs j cs[j] (List.getElem?_eq_getElem hj)
      have hcr2 : instPisWith fvsP (nestAbstract (pp.nestCtx fvsP envI.find? envI.consts) holes
          cs[j].1.type) = some crest := hcr
      rw [hcr2] at hcr'
      obtain rfl := Option.some.inj hcr'
      obtain ⟨nds, cur, htele, -⟩ := hd
      exact ⟨ks, nds, cur, ts, htele, hts⟩
  hgrp := by
    intro t ht I hI hm
    exact frame_grp_singleton hmkC rfl rfl (hok t ht).1 hI hm

end ConLeche.Model
