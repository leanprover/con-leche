module

public import InLeanProof.RecFireTr
public import InLeanProof.ProjBodiesTr
public import InLeanProof.StepPres
/- `ConstantInfo.name`/`isInductive`/`isCtor` are read through their bodies. -/
import all Lean.Declaration
import ConLeche.Verify.Cached.WalkersC

/-!
# `BlockPresObl` and the block's step (task #451, lanes P3r and follow-master)

An accepted block (`checkIndDeclC`: `readBlock = .ok p`, `genEntriesAgree`
and `checkBlockKS` accepted; a pinned basis block takes the same route)
installs, on con-leche's side, `blockConstants (trShape p)` and
`blockTables (trShape p)`; InLean adds the generated constants.  This file
relates the two at every generated constant's name, which is what
`presI_group` needs (`blockPresOblP`), and assembles the block's step
(`indGroupPresBP`).

**The statements are `BlockPresObl`/`IndGroupPresB` with three more
premises** (findings of this lane, see DESIGN.md "Lane P3r"):
* `fe.pending = []`.  `IndGroupPresB` is false at an environment carrying
  a stale block mark at one of the block's names: InLean then reads the
  installed former's capabilities and table at the mark (`capsOf`,
  `tableFields?`), con-leche at the shape.  The checker's environments outside
  a block's job have no mark (`FEnv.pending` defaults to `[]`, `checkDecl`
  builds `fe` without one), so P4 has it.
* `fe.sees` of every generated constant (`BlockPresObl` lacks it;
  `IndGroupPresB` has it): a hidden constructor is not found where the
  former's clause asks for it.
* `ProjBodiesAll`: every projection body InLean builds for the block's
  structures is in range, and so are its parameter variables (`projBodyOk`,
  `ProjBodiesTr.lean`).  InLean checks it
  beside `FEnv.projBodiesInRange` (`projBodiesAllOk`), so `IndGroupPresBP`
  takes that `Bool` and `projBodiesAll_of_ok` reads the premise off it.

**How the entries are read.**  The recogniser's record is the block's split
(`readBlock_spec`); the block check's recursor-name stage gives the split's
counts and constructor grouping (`checkBlockKS_cover`); `genEntriesAgree`
(`GenAgree`) gives each generated entry's data.  The block's names are
distinct (the generated constants' are), so `constNamed?` finds the very
constant of the split, and con-leche's install has the block's names in the
same order (`blockConstants_names`), so its lookups find the installed
constant of the same name.
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## Lists with distinct keys -/

theorem eq_of_map_nodup {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, hnd, a, b, ha, hb, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · exact absurd (by rw [h]; exact List.mem_map_of_mem hb') hnd.1
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd (by rw [← h]; exact List.mem_map_of_mem ha') hnd.1
      · exact eq_of_map_nodup f hnd.2 ha' hb' h

theorem find?_key {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) {l : List α}
    (hnd : (l.map f).Nodup) {a : α} (ha : a ∈ l) : l.find? (fun x => f x == f a) = some a := by
  cases h : l.find? (fun x => f x == f a) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (by simp) (h a ha)
  | some b =>
    have hb := List.mem_of_find?_eq_some h
    have hfb : f b = f a := by simpa using List.find?_some h
    rw [eq_of_map_nodup f hnd hb ha hfb]

theorem find?_key_none {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) {l : List α} {y : β}
    (hy : y ∉ l.map f) : l.find? (fun x => f x == y) = none := by
  rw [List.find?_eq_none]
  intro x hx he
  exact hy (by simpa using ⟨x, hx, (by simpa using he : f x = y)⟩)

theorem constNamed?_mem {l : List Lean.ConstantInfo} {n : Name} {ci : Lean.ConstantInfo}
    (h : constNamed? l n = some ci) : ci ∈ l ∧ ci.name = n := by
  unfold constNamed? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem constNamed?_of_mem {l : List Lean.ConstantInfo} (hnd : (l.map (·.name)).Nodup)
    {ci : Lean.ConstantInfo} (h : ci ∈ l) : constNamed? l ci.name = some ci := by
  unfold constNamed?
  exact find?_key (fun c : Lean.ConstantInfo => c.name) hnd h

/-! ## The stored block -/

theorem storedBlock_perm {consts : Array Lean.ConstantInfo}
    (hnd : (consts.toList.map (·.name)).Nodup)
    (h : ∀ ci ∈ consts.toList, ci ∈ storedBlock consts) : (storedBlock consts).Perm consts.toList := by
  classical
  have hl : consts.toList.Nodup :=
    List.Pairwise.of_map (fun c : Lean.ConstantInfo => c.name) (fun a b h he => h (he ▸ rfl)) hnd
  have hsub : ∀ ci ∈ storedBlock consts, ci ∈ consts.toList := by
    intro ci hci
    unfold storedBlock at hci
    simp only [Array.toList_append, Array.toList_filter, List.mem_append, List.mem_filter] at hci
    rcases hci with (h | h) | h <;> exact h.1
  rw [List.perm_ext_iff_of_nodup ?_ hl]
  · intro a; exact ⟨hsub a, h a⟩
  · unfold storedBlock
    simp only [Array.toList_append, Array.toList_filter]
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hl.filter _, hl.filter _, ?_⟩, hl.filter _, ?_⟩
    · intro a ha b hb he
      subst he
      simp only [List.mem_filter] at ha hb
      cases a <;> simp_all [Lean.ConstantInfo.isInductive, Lean.ConstantInfo.isCtor]
    · intro a ha b hb he
      subst he
      simp only [List.mem_append, List.mem_filter] at ha hb
      cases a <;> simp_all [Lean.ConstantInfo.isInductive, Lean.ConstantInfo.isCtor]

/-- A declaration group headed by a former reads as an inductive block at the
first former's parameter count. -/
theorem toDecl_ind {v : InductiveVal} {rest : List Lean.ConstantInfo} {d : ConLeche.Declaration}
    (h : toDecl (.inductInfo v :: rest) = some d) :
    ∃ cb, toBlock (.inductInfo v :: rest) = some cb ∧ d = .indDecl cb v.numParams := by
  simp only [toDecl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨cb, hcb, rfl⟩ := h
  exact ⟨cb, hcb, rfl⟩

/-! ## The recogniser's members -/

theorem mkMembers_facts : ∀ (cvTs : List ConstantVal) (nIdxs : List Nat)
    (groups : List (List (ConstantVal × Nat))),
    (mkMembers cvTs nIdxs groups).length = cvTs.length →
    (mkMembers cvTs nIdxs groups).map (·.cvT) = cvTs ∧
      ∀ ms ∈ mkMembers cvTs nIdxs groups, ms.declared = ms.cvT ∧ ms.ctors ∈ groups
  | [], _, _, _ => by simp [mkMembers]
  | _ :: _, [], _, h => by simp [mkMembers] at h
  | _ :: _, _ :: _, [], h => by simp [mkMembers] at h
  | c :: cs, n :: ns, g :: gs, h => by
    have ih := mkMembers_facts cs ns gs (by simpa [mkMembers] using h)
    simp only [mkMembers, List.zip_cons_cons, List.map_cons] at ih ⊢
    refine ⟨by rw [ih.1], ?_⟩
    intro ms hms
    rcases List.mem_cons.1 hms with rfl | hms
    · exact ⟨rfl, List.mem_cons_self⟩
    · exact ⟨(ih.2 ms hms).1, List.mem_cons_of_mem _ (ih.2 ms hms).2⟩

/-! ## con-leche's install of a recognised block -/

theorem blockFormers_names (p : ConLeche.BlockShape) (isRec : Bool) :
    (ConLeche.blockFormers p isRec).map (·.name) = p.members.map (·.declared.name) := by
  unfold ConLeche.blockFormers
  rw [List.map_map]
  have : ((·.name) ∘ fun (x : ConLeche.ConstantVal × Nat) =>
      ConLeche.ConstantInfo.indInfo x.1 (ConLeche.blockCapsAt p x.2 isRec)) =
      (·.name) ∘ Prod.fst := by funext x; rfl
  rw [this, ← List.map_map, List.zipIdx_map_fst, List.map_map]; rfl

theorem blockCtors_names (p : ConLeche.BlockShape) :
    (ConLeche.blockCtors p).map (·.name) = p.allCtors.map (·.1.name) := by
  unfold ConLeche.blockCtors; rw [List.map_map]; rfl

theorem blockRecs_names (p : ConLeche.BlockShape) : ∀ (rcs : List ConLeche.RecShape),
    (ConLeche.blockRecs p rcs).map (·.name) = rcs.map (·.cvR.name)
  | [] => rfl
  | rc :: rest => by
    simp only [ConLeche.blockRecs, List.map_cons, blockRecs_names p rest]; rfl

theorem blockFormers_mem (p : ConLeche.BlockShape) (isRec : Bool) {i : Nat}
    (hi : i < p.members.length) :
    .indInfo p.members[i].declared (ConLeche.blockCapsAt p i isRec) ∈ ConLeche.blockFormers p isRec := by
  unfold ConLeche.blockFormers
  refine List.mem_map.2 ⟨(p.members[i].declared, i), ?_, rfl⟩
  rw [List.mem_zipIdx_iff_getElem?]
  simp [hi]

theorem blockCtors_mem (p : ConLeche.BlockShape) {c : ConLeche.ConstantVal × Nat}
    (hc : c ∈ p.allCtors) : .ctorInfo c.1 p.nP c.2 ∈ ConLeche.blockCtors p := by
  unfold ConLeche.blockCtors
  exact List.mem_map.2 ⟨c, hc, rfl⟩

theorem blockRecs_mem (p : ConLeche.BlockShape) : ∀ {rcs : List ConLeche.RecShape} {rc : ConLeche.RecShape},
    rc ∈ rcs → .recInfo rc.cvR rc.mI rc.rP rc.isK
      (rc.rules.map ({ · with fire := ConLeche.recFire p rc })) ∈ ConLeche.blockRecs p rcs
  | [], _, h => absurd h List.not_mem_nil
  | x :: rest, rc, h => by
    simp only [ConLeche.blockRecs]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (blockRecs_mem p h)

/-- The table con-leche installs for a member, if any. -/
@[expose] def blockTableOf (p : ConLeche.BlockShape) (ms : ConLeche.MemberShape) : Option ConLeche.ProjTable :=
  match ms.structCtor? with
  | some c =>
    (ConLeche.structProjBodies ms.declared.name p.nP c.2 c.1.type).map fun bodies =>
      ⟨ms.declared.name, p.lps, p.nP, c.1.name, c.2, bodies⟩
  | none => none

theorem blockTables_names (p : ConLeche.BlockShape) : ∀ {Ms : List ConLeche.MemberShape}
    {Q : List ConLeche.ProjTable}, ConLeche.blockTables p Ms = some Q →
    (Q.map (·.structName)).Sublist (Ms.map (·.declared.name))
  | [], Q, h => by simp only [ConLeche.blockTables, Option.some.injEq] at h; subst h; simp
  | ms :: rest, Q, h => by
    simp only [ConLeche.blockTables, List.map_cons] at h ⊢
    split at h
    · cases hb : ConLeche.structProjBodies ms.declared.name p.nP _ _ with
      | none => rw [hb] at h; cases h
      | some bodies =>
        rw [hb] at h
        simp only [Option.bind_some, Option.map_eq_some_iff] at h
        obtain ⟨Q', hQ', rfl⟩ := h
        simp only [List.map_cons]; exact (blockTables_names p hQ').cons_cons _
    · exact (blockTables_names p h).cons _

theorem blockTables_find (p : ConLeche.BlockShape) : ∀ {Ms : List ConLeche.MemberShape}
    {Q : List ConLeche.ProjTable}, ConLeche.blockTables p Ms = some Q →
    (Ms.map (·.declared.name)).Nodup → ∀ {ms}, ms ∈ Ms →
      Q.find? (·.structName == ms.declared.name) = blockTableOf p ms
  | [], _, _, _, _, h => absurd h List.not_mem_nil
  | x :: rest, Q, hQ, hnd, ms, hms => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hnone : ∀ y, y ∈ rest → y.declared.name ≠ x.declared.name := by
      intro y hy he; exact hnd.1 (he ▸ List.mem_map_of_mem hy)
    -- the rest's tables, and the head's
    have hsplit : ∃ Q', ConLeche.blockTables p rest = some Q' ∧
        Q = (match blockTableOf p x with | some t => [t] | none => []) ++ Q' := by
      simp only [ConLeche.blockTables] at hQ
      unfold blockTableOf
      split at hQ
      · rename_i c hc
        rw [hc]
        cases hb : ConLeche.structProjBodies x.declared.name p.nP c.2 c.1.type with
        | none => rw [hb] at hQ; cases hQ
        | some bodies =>
          rw [hb] at hQ
          simp only [Option.bind_some, Option.map_eq_some_iff] at hQ
          obtain ⟨Q', hQ', rfl⟩ := hQ
          exact ⟨Q', hQ', by simp [hb]⟩
      · rename_i hc
        rw [hc]
        exact ⟨Q, hQ, by simp⟩
    obtain ⟨Q', hQ', rfl⟩ := hsplit
    have hrest : Q'.find? (·.structName == x.declared.name) = none := by
      apply find?_key_none
      intro hm
      exact hnd.1 ((blockTables_names p hQ').subset hm)
    rcases List.mem_cons.1 hms with rfl | hms
    · cases hb : blockTableOf p ms with
      | none => simp only [List.nil_append]; exact hrest
      | some t =>
        have ht : t.structName = ms.declared.name := by
          unfold blockTableOf at hb
          split at hb
          · simp only [Option.map_eq_some_iff] at hb
            obtain ⟨_, -, rfl⟩ := hb; rfl
          · cases hb
        simp [ht]
    · have ih := blockTables_find p hQ' hnd.2 hms
      have hne : ms.declared.name ≠ x.declared.name := hnone ms hms
      cases hb : blockTableOf p x with
      | none => simpa using ih
      | some t =>
        have ht : t.structName = x.declared.name := by
          unfold blockTableOf at hb
          split at hb
          · simp only [Option.map_eq_some_iff] at hb
            obtain ⟨_, -, rfl⟩ := hb; rfl
          · cases hb
        simp only [List.cons_append, List.nil_append, List.find?_cons, ht]
        rw [show (x.declared.name == ms.declared.name) = false by simpa using hne.symm]
        exact ih

theorem find?_reverse_key {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) {l : List α}
    (hnd : (l.map f).Nodup) (y : β) :
    l.reverse.find? (fun x => f x == y) = l.find? (fun x => f x == y) := by
  cases h : l.find? (fun x => f x == y) with
  | none =>
    rw [List.find?_eq_none] at h ⊢
    intro x hx; exact h x (List.mem_reverse.1 hx)
  | some a =>
    have ha := List.mem_of_find?_eq_some h
    have hfa : f a = y := by simpa using List.find?_some h
    subst hfa
    exact find?_key f (by rw [List.map_reverse]; exact List.pairwise_reverse.2 (hnd.imp fun h he => h he.symm)) (List.mem_reverse.2 ha)

/-! ## The recognised block, read off the run -/

/-- **What an accepted recognised block gives**, gathered: the split, the
record (`readBlock_spec`), the counts and grouping (`checkBlockKS_cover`),
the generated entries (`GenAgree`), distinct names and closed readings. -/
structure RecogCtx (block : List Lean.ConstantInfo) (p : InLean.BlockShape) (nP : Nat)
    (cvTs : List ConstantVal) (cs : List (ConstantVal × Nat × Nat)) (rs : List RecParts) : Prop where
  ndB : (block.map (·.name)).Nodup
  ok : ∀ ci ∈ block, CIOk ci
  okT : ∀ ci ∈ block, okC ci.toConstantVal.type = true
  hp : InLean.readBlock nP block = .ok p
  pnP : p.nP = nP
  ga : GenAgree p block
  split : InLean.blockSplit block = some (cvTs, cs, rs)
  ctorsN : p.allCtors.map (·.1.name) = cs.map (·.1.name)
  ndM : p.memberNames.Nodup
  cvT : p.members.map (·.cvT) = cvTs
  decl : ∀ ms ∈ p.members, ms.declared = ms.cvT
  ctorMem : ∀ ms ∈ p.members, ∀ c ∈ ms.ctors, c ∈ cs.map fun c => (c.1, c.2.2)
  recs : p.recs = rs.map (mkRec (cvTs.map (·.name)))
  lps : ∀ ms ∈ p.members, ms.cvT.levelParams = p.lps

theorem blockSplit_formers : ∀ {block : List Lean.ConstantInfo} {cvTs cs rs},
    InLean.blockSplit block = some (cvTs, cs, rs) →
    ∀ c ∈ cvTs, ∃ v, Lean.ConstantInfo.inductInfo v ∈ block ∧ v.toConstantVal = c
  | .inductInfo v :: rest, cvTs, cs, rs, h => by
    simp only [InLean.blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨q, h1, h2⟩ := h
    obtain ⟨q1, q2, q3⟩ := q
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl, rfl⟩ := h2
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨v, List.mem_cons_self, rfl⟩
    · obtain ⟨w, hw, he⟩ := blockSplit_formers h1 c hc
      exact ⟨w, List.mem_cons_of_mem _ hw, he⟩
  | [], cvTs, cs, rs, h | .recInfo _ :: _, cvTs, cs, rs, h | .ctorInfo _ :: _, cvTs, cs, rs, h
  | .axiomInfo _ :: _, cvTs, cs, rs, h | .defnInfo _ :: _, cvTs, cs, rs, h
  | .thmInfo _ :: _, cvTs, cs, rs, h | .opaqueInfo _ :: _, cvTs, cs, rs, h
  | .quotInfo _ :: _, cvTs, cs, rs, h => by
    unfold InLean.blockSplit at h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨q, h1, rfl, rfl, rfl⟩ := h
    simp

theorem recogCtx_of {μ : CheckMode} {fe : InLean.FEnv} {block : List Lean.ConstantInfo}
    {p : InLean.BlockShape} {nP : Nat} {s s₁ s' : InLean.CState}
    (hndB : (block.map (·.name)).Nodup) (hR : ∀ ci ∈ block, CIRange ci) (cb : List ConLeche.ConstantInfo)
    (htb : toBlock block = some cb) (hp : InLean.readBlock nP block = .ok p)
    (hgen : (genEntriesAgree p block) s = .ok ((), s₁))
    (hks : (checkBlockKS μ fe block p) s₁ = .ok ((), s')) :
    ∃ cvTs cs rs, RecogCtx block p nP cvTs cs rs := by
  obtain ⟨cvTs, cs, rs, hsp, hlenT, -, hctorsN, -, hndM⟩ := checkBlockKS_cover hks
  obtain ⟨cvT0, tl, cs', rs', nIdxs, hsp', hpnP, hmems, hrecs, hlps⟩ := readBlock_spec hp
  rw [hsp] at hsp'
  simp only [Option.some.injEq, Prod.mk.injEq] at hsp'
  obtain ⟨rfl, rfl, rfl⟩ := hsp'
  obtain ⟨hmcvT, hmdecl⟩ := mkMembers_facts _ _ _ (by rw [← hmems]; exact hlenT.symm)
  rw [← hmems] at hmcvT hmdecl
  have hkinds := (toBlock_eq htb hR).2
  refine ⟨cvT0 :: tl, cs, rs, ⟨hndB, toBlock_CIOk htb hR, fun ci h => (hkinds ci h).2, hp, hpnP,
    genEntriesAgree_facts hgen, hsp, hctorsN, hndM, hmcvT, fun ms h => (hmdecl ms h).1, ?_, hrecs,
    ?_⟩⟩
  · intro ms hms c hc
    have hg := (hmdecl ms hms).2
    exact blockGroups_sub _ _ _ _ _ _ hg c hc
  · intro ms hms
    have h0 : p.lps = cvT0.levelParams := by
      unfold InLean.BlockShape.lps
      cases hm : p.members with
      | nil => rw [hm] at hmcvT; cases hmcvT
      | cons m ms' =>
        rw [hm] at hmcvT
        simp only [List.map_cons, List.cons.injEq] at hmcvT
        simp [hmcvT.1]
    rw [h0]
    exact hlps _ (hmcvT ▸ List.mem_map_of_mem hms)

section Ctx
variable {block : List Lean.ConstantInfo} {p : InLean.BlockShape} {nP : Nat}
  {cvTs : List ConstantVal} {cs : List (ConstantVal × Nat × Nat)} {rs : List RecParts}

theorem RecogCtx.uniq (C : RecogCtx block p nP cvTs cs rs) {a b : Lean.ConstantInfo}
    (ha : a ∈ block) (hb : b ∈ block) (h : a.name = b.name) : a = b :=
  eq_of_map_nodup (·.name) C.ndB ha hb h

/-- A member's former, the generated entry. -/
theorem RecogCtx.former (C : RecogCtx block p nP cvTs cs rs) {ms : InLean.MemberShape}
    (hms : ms ∈ p.members) : ∃ v, Lean.ConstantInfo.inductInfo v ∈ block ∧
      v.toConstantVal = ms.cvT ∧ v.all = p.memberNames ∧ v.numParams = p.nP ∧
      v.numIndices = ms.nIdx ∧ v.ctors = ms.ctors.map (·.1.name) ∧ v.isRec = blockIsRec p := by
  obtain ⟨v, hv, h1, h2, h3, h4, h5⟩ := C.ga.former ms hms
  obtain ⟨hvb, hvn⟩ := constNamed?_mem hv
  have hcv : ms.cvT ∈ cvTs := C.cvT ▸ List.mem_map_of_mem hms
  obtain ⟨ci, hci, hcicv⟩ := (blockSplit_sub C.split).1 _ hcv
  have : ci = .inductInfo v := C.uniq hci hvb (by rw [ci_cv_name, hcicv]; exact hvn.symm)
  subst this
  exact ⟨v, hvb, hcicv, h1, h2, h3, h4, h5⟩

/-- A member's constructor, the generated entry. -/
theorem RecogCtx.ctorW (C : RecogCtx block p nP cvTs cs rs) {ms : InLean.MemberShape}
    (hms : ms ∈ p.members) {c : ConstantVal × Nat} (hc : c ∈ ms.ctors) :
    ∃ w, Lean.ConstantInfo.ctorInfo w ∈ block ∧ w.toConstantVal = c.1 ∧ w.numParams = p.nP ∧
      w.numFields = c.2 := by
  obtain ⟨w, hw, h1, h2, -⟩ := C.ga.ctor ms hms c hc
  obtain ⟨hwb, hwn⟩ := constNamed?_mem hw
  obtain ⟨x, hx, hxc⟩ := List.mem_map.1 (C.ctorMem ms hms c hc)
  obtain ⟨ci, hci, hcicv⟩ := (blockSplit_sub C.split).2 x hx
  have hx1 : x.1 = c.1 := by rw [← hxc]
  have : ci = .ctorInfo w := C.uniq hci hwb (by rw [ci_cv_name, hcicv, hx1]; exact hwn.symm)
  subst this
  exact ⟨w, hwb, hcicv.trans hx1, h1, h2⟩

/-- A block former is a member's. -/
theorem RecogCtx.ofFormer (C : RecogCtx block p nP cvTs cs rs) {v : InductiveVal}
    (h : Lean.ConstantInfo.inductInfo v ∈ block) :
    ∃ i, ∃ hi : i < p.members.length, p.members[i].cvT = v.toConstantVal := by
  rcases blockSplit_mem C.split _ h with ⟨w, hw, hm⟩ | ⟨w, hw, _⟩ | ⟨w, hw, _⟩
  · cases hw
    rw [← C.cvT] at hm
    obtain ⟨ms, hms, he⟩ := List.mem_map.1 hm
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hms
    exact ⟨i, hi, he⟩
  · cases hw
  · cases hw

/-- A block constructor is a member's. -/
theorem RecogCtx.ofCtor (C : RecogCtx block p nP cvTs cs rs) {v : ConstructorVal}
    (h : Lean.ConstantInfo.ctorInfo v ∈ block) :
    ∃ ms ∈ p.members, ∃ c ∈ ms.ctors, c.1 = v.toConstantVal ∧ v.numParams = p.nP ∧
      v.numFields = c.2 := by
  rcases blockSplit_mem C.split _ h with ⟨w, hw, _⟩ | ⟨w, hw, hm⟩ | ⟨w, hw, _⟩
  · cases hw
  · cases hw
    have hn : v.name ∈ p.allCtors.map (·.1.name) := by
      rw [C.ctorsN]; exact List.mem_map_of_mem (f := (·.1.name)) hm
    obtain ⟨c, hc, hcn⟩ := List.mem_map.1 hn
    obtain ⟨g, hg, hcg⟩ := List.mem_flatten.1 hc
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.1 hg
    obtain ⟨w, hwb, h1, h2, h3⟩ := C.ctorW hms hcg
    have : Lean.ConstantInfo.ctorInfo w = .ctorInfo v :=
      C.uniq hwb h (by show w.name = v.name; rw [← hcn, ← h1])
    cases this
    exact ⟨ms, hms, c, hcg, h1.symm, h2, h3⟩
  · cases hw

/-- A block recursor is a record's. -/
theorem RecogCtx.ofRec (C : RecogCtx block p nP cvTs cs rs) {v : RecursorVal}
    (h : Lean.ConstantInfo.recInfo v ∈ block) :
    mkRec (cvTs.map (·.name)) (v.toConstantVal, majorIdxOf v, rulePrefixOf v, v.k, v.rules) ∈ p.recs ∧
      v.all = p.memberNames := by
  rcases blockSplit_mem C.split _ h with ⟨w, hw, _⟩ | ⟨w, hw, _⟩ | ⟨w, hw, hm⟩
  · cases hw
  · cases hw
  · cases hw
    have hrc : mkRec (cvTs.map (·.name)) (v.toConstantVal, majorIdxOf v, rulePrefixOf v, v.k, v.rules)
        ∈ p.recs := by rw [C.recs]; exact List.mem_map_of_mem hm
    refine ⟨hrc, ?_⟩
    obtain ⟨w, hw, hall⟩ := C.ga.recs _ hrc
    obtain ⟨hwb, hwn⟩ := constNamed?_mem hw
    have : Lean.ConstantInfo.recInfo w = .recInfo v := C.uniq hwb h hwn
    cases this
    exact hall

theorem RecogCtx.memberNames (C : RecogCtx block p nP cvTs cs rs) :
    p.memberNames = cvTs.map (·.name) := by
  rw [← C.cvT, List.map_map]; rfl

/-! ## con-leche's install of the record, by name -/

theorem trShape_members_getElem (p : InLean.BlockShape) {i : Nat} (hi : i < p.members.length) :
    (trShape p).members[i]'(by simpa [trShape] using hi) = trMember p.members[i] := by
  simp [trShape]

theorem trShape_members_getD (p : InLean.BlockShape) {i : Nat} (hi : i < p.members.length) :
    (trShape p).members.getD i default = trMember p.members[i] := by
  simp [trShape, List.getD_eq_getElem?_getD, hi]

theorem structCtor_tr (ms : InLean.MemberShape) :
    (trMember ms).structCtor? = ms.structCtor?.map trCtor := by
  unfold ConLeche.MemberShape.structCtor? InLean.MemberShape.structCtor?
  simp only [trMember]
  cases h : ms.ctors with
  | nil => rfl
  | cons c rest =>
    cases rest with
    | nil =>
      simp only [List.map_cons, List.map_nil]
      by_cases hn : (ms.nIdx == 0) = true <;> simp [hn]
    | cons _ _ => rfl

/-- **con-leche's install has the block's names, in order.** -/
theorem RecogCtx.news_names (C : RecogCtx block p nP cvTs cs rs) :
    (ConLeche.blockConstants (trShape p)).map (·.name) = (block.map (·.name)).map toName := by
  have h1 : (trShape p).members.map (·.declared.name) = (cvTs.map (·.name)).map toName := by
    simp only [trShape, List.map_map]
    rw [← C.cvT, List.map_map]
    apply List.map_congr_left
    intro ms hms
    simp [trMember, C.decl ms hms]
  have h3 : (trShape p).recs.map (·.cvR.name) = (rs.map (·.1.name)).map toName := by
    simp only [trShape, List.map_map, C.recs]
    rfl
  unfold ConLeche.blockConstants
  rw [List.map_append, List.map_append, blockFormers_names, blockCtors_names, blockRecs_names,
    trShape_allCtorNames, C.ctorsN, blockSplit_names C.split, h1, h3]
  simp only [List.map_append]

/-- The table names con-leche installs are member names, distinct. -/
theorem RecogCtx.tab_names (C : RecogCtx block p nP cvTs cs rs) :
    ((trShape p).members.map (·.declared.name)) = (cvTs.map (·.name)).map toName ∧
      ((trShape p).members.map (·.declared.name)).Nodup := by
  have h : ((trShape p).members.map (·.declared.name)) = (cvTs.map (·.name)).map toName := by
    simp only [trShape, List.map_map]
    rw [← C.cvT, List.map_map]
    apply List.map_congr_left
    intro ms hms
    simp [trMember, C.decl ms hms]
  refine ⟨h, ?_⟩
  rw [h, ← C.memberNames]
  exact List.Pairwise.map _ (fun a b hab he => hab (toName_inj he)) C.ndM

/-! ## The entries -/

section Entries
variable {fe' : InLean.FEnv}

theorem LRel_map_right {α γ : Type} {R : α → γ → Prop} {g : α → γ} :
    ∀ (l : List α), (∀ a ∈ l, R a (g a)) → LRel R l (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a List.mem_cons_self)
      (LRel_map_right l fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem CVRel_trCV {v : ConstantVal} (h : okC v.type = true) : CVRel v (trCV v) :=
  ⟨rfl, rfl, fvarS_of_toExprC (toExpr_of_okE _ h), RangeOk_of_okE h, toExpr_of_okE _ h⟩

theorem fieldsOf_nopend (hpend : fe'.pending = []) {v : InductiveVal} {c : Name} {w : ConstructorVal}
    (h : fe'.find? c = some (.ctorInfo w)) : fe'.fieldsOf v c = w.numFields := by
  unfold InLean.FEnv.fieldsOf InLean.FEnv.pendingFields?
  rw [hpend]
  simp [InLean.FEnv.pendingFields?.go, h]

theorem isPending_nopend (hpend : fe'.pending = []) (n : Name) : fe'.isPending n = false := by
  simp [InLean.FEnv.isPending, InLean.FEnv.pendingFields?, hpend, InLean.FEnv.pendingFields?.go]

/-- **Every generated constant has its installed counterpart**, related. -/
theorem RecogCtx.entry (C : RecogCtx block p nP cvTs cs rs) (hpend : fe'.pending = [])
    (hfind : ∀ ci ∈ block, fe'.find? ci.name = some ci) :
    ∀ ci ∈ block, ∃ cci ∈ ConLeche.blockConstants (trShape p),
      cci.name = toName ci.name ∧ EntryRelI fe' ci cci := by
  intro ci hci
  have hcv : ∀ {w : ConstructorVal}, Lean.ConstantInfo.ctorInfo w ∈ block →
      fe'.find? w.name = some (.ctorInfo w) := fun h => hfind _ h
  rcases blockSplit_mem C.split ci hci with ⟨v, rfl, -⟩ | ⟨v, rfl, -⟩ | ⟨v, rfl, -⟩
  · -- a former
    obtain ⟨i, hi, hiv⟩ := C.ofFormer hci
    obtain ⟨v', hv'b, hv'cv, hall, hnP, hidx, hctors, hrec⟩ := C.former (List.getElem_mem hi)
    have : Lean.ConstantInfo.inductInfo v' = .inductInfo v :=
      C.uniq hv'b hci (by show v'.toConstantVal.name = v.toConstantVal.name; rw [hv'cv, hiv])
    cases this
    have hokT : okC v.type = true := C.okT _ hci
    have hiP : i < (trShape p).members.length := by simpa [trShape] using hi
    refine ⟨_, List.mem_append_left _ (List.mem_append_left _
      (blockFormers_mem (trShape p) (ConLeche.blockIsRec (trShape p)) hiP)), ?_, ?_⟩
    · rw [trShape_members_getElem p hi]
      simp [trMember, C.decl _ (List.getElem_mem hi), hiv]; rfl
    · rw [trShape_members_getElem p hi]
      simp only [EntryRelI]
      have hdecl : (trMember p.members[i]).declared = trCV v.toConstantVal := by
        simp [trMember, C.decl _ (List.getElem_mem hi), hiv]
      rw [hdecl]
      refine ⟨CVRel_trCV hokT, ?_, .inr ?_⟩
      · rw [← ConLeche.Cached.blockIsRecC_eq, blockIsRec_tr]
        refine (toCaps_capsOf (mi := i) ?_ ?_ ?_ ?_ hrec ?_).symm
        · rw [trShape_members_getD p hi, hctors]
          simp [trMember, trCtor]
        · rw [trShape_members_getD p hi, hidx]; rfl
        · rw [hnP]; rfl
        · rw [trShape_memberNames, hall]
        · intro c cc hvc hcc
          rw [trShape_members_getD p hi] at hcc
          simp only [trMember] at hcc
          cases hms : p.members[i].ctors with
          | nil => rw [hms] at hcc; cases hcc
          | cons c0 rest =>
            rw [hms] at hcc
            cases rest with
            | cons _ _ => cases hcc
            | nil =>
              simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcc
              subst hcc
              rw [hctors, hms] at hvc
              simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvc
              subst hvc
              obtain ⟨w, hwb, hw1, -, hw3⟩ := C.ctorW (List.getElem_mem hi)
                (show c0 ∈ p.members[i].ctors by rw [hms]; exact List.mem_cons_self)
              have hf := hcv hwb
              rw [show w.name = c0.1.name by rw [← hw1]] at hf
              rw [fieldsOf_nopend hpend hf, hw3]; rfl
      · intro c hc
        rw [hctors] at hc
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
        obtain ⟨w, hwb, hw1, -, -⟩ := C.ctorW (List.getElem_mem hi) hc0
        have hf := hcv hwb
        rw [show w.name = c0.1.name by rw [← hw1]] at hf
        rw [hf]; rfl
  · -- a constructor
    obtain ⟨ms, hms, c, hc, hc1, hnP, hnF⟩ := C.ofCtor hci
    have hokT : okC v.type = true := C.okT _ hci
    have hmem : trCtor c ∈ (trShape p).allCtors := by
      simp only [trShape, ConLeche.BlockShape.allCtors, List.map_map, List.mem_flatten, List.mem_map]
      exact ⟨_, ⟨ms, hms, rfl⟩, by simp only [Function.comp_apply, trMember]; exact List.mem_map_of_mem hc⟩
    refine ⟨_, List.mem_append_left _ (List.mem_append_right _ (blockCtors_mem _ hmem)), ?_, ?_⟩
    · simp [trCtor, hc1]; rfl
    · simp only [EntryRelI, trCtor, hc1]
      exact ⟨CVRel_trCV hokT, by rw [hnP]; rfl, hnF.symm⟩
  · -- a recursor
    obtain ⟨hrc, hall⟩ := C.ofRec hci
    have hok := C.ok _ hci
    simp only [CIOk] at hok
    have hmem : trRec (mkRec (cvTs.map (·.name))
        (v.toConstantVal, majorIdxOf v, rulePrefixOf v, v.k, v.rules)) ∈ (trShape p).recs := by
      simp only [trShape]; exact List.mem_map_of_mem hrc
    refine ⟨_, List.mem_append_right _ (blockRecs_mem _ hmem), ?_, ?_⟩
    · simp [trRec, mkRec]; rfl
    · simp only [EntryRelI, RecRelI]
      refine ⟨trCV v.toConstantVal, _, rfl, CVRel_trCV hok.1, ?_⟩
      simp only [trRec, mkRec, List.map_map]
      apply LRel_map_right
      intro r hr
      refine ⟨⟨rfl, rfl, ?_⟩, fvarS_of_toExprC (toExpr_of_okE _ (hok.2 r hr)), RangeOk_of_okE (hok.2 r hr),
        toExpr_of_okE _ (hok.2 r hr)⟩
      exact recFire_tr (P := trShape p) (rc := mkRec (cvTs.map (·.name))
          (v.toConstantVal, majorIdxOf v, rulePrefixOf v, v.k, v.rules)) hok.1 (hall.trans C.memberNames)
        (by simp [ConLeche.BlockShape.k, trShape, ← C.cvT]) rfl rfl rfl rfl

theorem structCtor_ctors {ms : InLean.MemberShape} {c : Lean.ConstantVal × Nat}
    (h : ms.structCtor? = some c) : ms.ctors = [c] := by
  unfold InLean.MemberShape.structCtor? at h
  split at h
  · rename_i c' hc
    split at h
    · cases h; exact hc
    · cases h
  · cases h

/-- **InLean's tables built means master's are**: per structure member,
InLean's `structProjBodies` succeeds exactly where its telescope test does
(`hasPis`), which is master's bodies succeeding (`hasPis_iff_structProjBodies`). -/
theorem cblockTables_isSome (p : InLean.BlockShape) :
    ∀ (l : List InLean.MemberShape),
      (∀ ms ∈ l, ∀ c, ms.structCtor? = some c → toExprC c.1.type = some (trC c.1.type)) →
      (InLean.blockTables p l).isSome →
      (ConLeche.blockTables (trShape p) (l.map trMember)).isSome
  | [], _, _ => rfl
  | ms :: rest, hok, h => by
    have ih := cblockTables_isSome p rest (fun m hm => hok m (List.mem_cons_of_mem _ hm))
    simp only [List.map_cons, ConLeche.blockTables, structCtor_tr]
    simp only [InLean.blockTables] at h
    cases hsc : ms.structCtor? with
    | none =>
      simp only [hsc] at h
      exact ih h
    | some c =>
      have hc := hok ms List.mem_cons_self c hsc
      cases hb : InLean.structProjBodies ms.declared.name p.nP c.2 c.1.type with
      | none => simp only [hsc, hb, Option.bind_none] at h; cases h
      | some bodies =>
        simp only [hsc, hb, Option.bind_some, Option.isSome_map] at h
        have hpis : hasPis (p.nP + c.2) c.1.type = true := by
          unfold InLean.structProjBodies at hb
          split at hb
          · assumption
          · cases hb
        rw [hasPis_iff_structProjBodies (S := (trMember ms).declared.name) hc] at hpis
        obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.1 hpis
        simp only [Option.map_some, trCtor, trCV] at hcb ⊢
        rw [show (trShape p).nP = p.nP from rfl, hcb]
        simp only [Option.bind_some, Option.isSome_map]
        exact ih h

/-- **Every generated constant's table is related**: con-leche's table at its
name (`blockTables`, found by name) against what InLean reads off the former
and its constructor. -/
theorem RecogCtx.table (C : RecogCtx block p nP cvTs cs rs) (hpend : fe'.pending = [])
    (hfind : ∀ ci ∈ block, fe'.find? ci.name = some ci)
    (hsteps : ∀ v cv, Lean.ConstantInfo.inductInfo v ∈ block → v.ctors = [cv.name] →
      Lean.ConstantInfo.ctorInfo cv ∈ block →
      ∀ i < cv.numFields, projBodyOk v.name v.numParams i cv.type = true)
    {cQ : List ConLeche.ProjTable}
    (hcQ : ConLeche.blockTables (trShape p) (trShape p).members = some cQ) :
    ∀ ci ∈ block, TableRelI fe' ci.name
      (cQ.find? (·.structName == toName ci.name)) := by
  obtain ⟨htn, htnd⟩ := C.tab_names
  have hnotab : ∀ ci ∈ block, (∀ v, ci ≠ .inductInfo v) →
      cQ.find? (·.structName == toName ci.name) = none := by
    intro ci hci hk
    apply find?_key_none
    intro hm
    have hm' := (blockTables_names _ hcQ).subset hm
    rw [htn] at hm'
    obtain ⟨n, hn, hne⟩ := List.mem_map.1 hm'
    obtain ⟨cvT, hcvT, rfl⟩ := List.mem_map.1 hn
    obtain ⟨w, hwb, he⟩ := blockSplit_formers C.split _ hcvT
    have : Lean.ConstantInfo.inductInfo w = ci :=
      C.uniq hwb hci (by show w.toConstantVal.name = _; rw [he]; exact toName_inj hne)
    exact hk w this.symm
  intro ci hci
  rcases blockSplit_mem C.split ci hci with ⟨v, rfl, -⟩ | ⟨v, rfl, -⟩ | ⟨v, rfl, -⟩
  · -- a former
    obtain ⟨i, hi, hiv⟩ := C.ofFormer hci
    have hmsm := List.getElem_mem hi
    obtain ⟨v', hv'b, hv'cv, -, hnP, hidx, hctors, -⟩ := C.former hmsm
    have : Lean.ConstantInfo.inductInfo v' = .inductInfo v :=
      C.uniq hv'b hci (by show v'.toConstantVal.name = v.toConstantVal.name; rw [hv'cv, hiv])
    cases this
    have hiP : i < (trShape p).members.length := by simpa [trShape] using hi
    have hname : toName (Lean.ConstantInfo.inductInfo v).name =
        ((trShape p).members[i]'hiP).declared.name := by
      rw [trShape_members_getElem p hi]
      simp [trMember, C.decl _ hmsm, hiv]; rfl
    rw [hname, blockTables_find _ hcQ htnd (List.getElem_mem hiP), trShape_members_getElem p hi]
    have hfv := hfind _ hci
    unfold blockTableOf
    rw [structCtor_tr]
    generalize hms : p.members[i] = ms at hiv hnP hidx hctors hmsm
    cases hsc : ms.structCtor? with
    | none =>
      simp only [Option.map_none, TableRelI, InLean.FEnv.tableFields?]
      rw [show (Lean.ConstantInfo.inductInfo v).name = v.name from rfl] at hfv ⊢
      rw [hfv]
      simp only [isPending_nopend hpend, Bool.false_eq_true, ↓reduceIte]
      unfold InLean.MemberShape.structCtor? at hsc
      rw [hctors]
      cases hc : ms.ctors with
      | nil => rfl
      | cons c0 rest =>
        cases rest with
        | cons _ _ => rfl
        | nil =>
          rw [hc] at hsc
          simp only at hsc
          have h0 : (ms.nIdx == 0) = false := by
            cases h : (ms.nIdx == 0)
            · rfl
            · rw [h] at hsc; cases hsc
          simp [hidx, h0]
    | some c0 =>
      have hc0 : ms.ctors = [c0] ∧ ms.nIdx = 0 := by
        unfold InLean.MemberShape.structCtor? at hsc
        cases hc : ms.ctors with
        | nil => rw [hc] at hsc; cases hsc
        | cons c1 rest =>
          cases rest with
          | cons _ _ => rw [hc] at hsc; cases hsc
          | nil =>
            rw [hc] at hsc
            simp only at hsc
            cases h : (ms.nIdx == 0)
            · rw [h] at hsc; cases hsc
            · rw [h] at hsc
              simp only [↓reduceIte, Option.some.injEq] at hsc
              exact ⟨by rw [hsc], by simpa using h⟩
      obtain ⟨w, hwb, hw1, hw2, hw3⟩ := C.ctorW hmsm (show c0 ∈ ms.ctors by rw [hc0.1]; simp)
      have hwname : w.name = c0.1.name := by rw [← hw1]
      have hfw := hfind _ hwb
      rw [show (Lean.ConstantInfo.ctorInfo w).name = c0.1.name from hwname] at hfw
      have hvc : v.ctors = [c0.1.name] := by rw [hctors, hc0.1]; rfl
      have hvi : v.numIndices = 0 := by rw [hidx, hc0.2]
      have hokw : okC w.type = true := C.okT _ hwb
      have hpis := hasPis_iff_structProjBodies (S := toName ms.cvT.name) (nP := p.nP) (nF := c0.2)
        (toExpr_of_okE _ hokw)
      have hwt : trC w.type = trC c0.1.type := by
        rw [show w.type = w.toConstantVal.type from rfl, hw1]
      have hdn : (trMember ms).declared.name = toName ms.cvT.name := by
        simp [trMember, C.decl _ hmsm]
      simp only [Option.map_some, trCtor, trCV_type, hdn]
      rw [← hwt]
      cases hb : ConLeche.structProjBodies (toName ms.cvT.name) (trShape p).nP c0.2 (trC w.type) with
      | none =>
        simp only [Option.map_none, TableRelI, InLean.FEnv.tableFields?]
        rw [show (Lean.ConstantInfo.inductInfo v).name = v.name from rfl] at hfv ⊢
        rw [hfv]
        simp only [isPending_nopend hpend, Bool.false_eq_true, ↓reduceIte, hvc, hvi]
        simp only [beq_self_eq_true, ↓reduceIte, hfw]
        rw [hnP, hw3]
        have : (trShape p).nP = p.nP := rfl
        rw [this] at hb
        rw [hpis, show trE (fun _ => none) w.type = trC w.type from rfl, hb]; rfl
      | some bodies =>
        simp only [Option.map_some, TableRelI]
        refine ⟨v, c0.1.name, w, hfv, isPending_nopend hpend _, hvc, hvi, hfw, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
        · rw [hnP, hw3, hpis, show trE (fun _ => none) w.type = trC w.type from rfl]
          rw [show (trShape p).nP = p.nP from rfl] at hb; rw [hb]; rfl
        · show toName ms.cvT.name = toName v.name
          rw [hiv]
        · show (trShape p).lps = v.levelParams.map toName
          rw [show v.levelParams = ms.cvT.levelParams by rw [hiv], C.lps _ hmsm]
          unfold ConLeche.BlockShape.lps InLean.BlockShape.lps
          cases hm : p.members with
          | nil => simp [trShape, hm]
          | cons m _ => simp [trShape, hm, trMember]
        · show p.nP = v.numParams; rw [hnP]
        · rfl
        · show c0.2 = w.numFields; rw [hw3]
        · intro j hj
          have hsv := hsteps v w hci (by rw [hvc, hwname]) hwb j hj
          rw [show v.name = ms.cvT.name by rw [hiv]] at hsv
          rw [show (Lean.ConstantInfo.inductInfo v).name = ms.cvT.name by
            show v.toConstantVal.name = _; rw [hiv]]
          rw [show (trShape p).nP = v.numParams by rw [hnP]; rfl] at hb
          exact projBodyAt_tr hsv (RangeOk_of_okE hokw) (toExpr_of_okE _ hokw) hb (by rw [← hw3]; exact hj)
  · rw [hnotab _ hci (fun w h => by cases h)]
    simp only [TableRelI, InLean.FEnv.tableFields?, hfind _ hci]
  · rw [hnotab _ hci (fun w h => by cases h)]
    simp only [TableRelI, InLean.FEnv.tableFields?, hfind _ hci]

end Entries

end Ctx

/-! ## The statements -/

/-- **Every projection body InLean builds for the generated structures is in
range, and so are its parameter variables** (`projBodyOk`; see
`ProjBodiesTr.lean`). -/
@[expose] def ProjBodiesAll (consts : Array Lean.ConstantInfo) : Prop :=
  ∀ v cv, Lean.ConstantInfo.inductInfo v ∈ consts.toList → v.ctors = [cv.name] →
    Lean.ConstantInfo.ctorInfo cv ∈ consts.toList →
    ∀ i < cv.numFields, projBodyOk v.name v.numParams i cv.type = true

/-- **`ProjBodiesAll` from InLean's check** (`projBodiesAllOk`, which
`checkInductiveC` runs on the generated constants). -/
theorem projBodiesAll_of_ok {consts : Array Lean.ConstantInfo}
    (h : InLean.projBodiesAllOk consts = true) : ProjBodiesAll consts := by
  intro v cv hv hc hcv i hi
  unfold InLean.projBodiesAllOk at h
  rw [Array.all_eq_true_iff_forall_mem] at h
  have h1 := h _ (Array.mem_toList_iff.1 hv)
  simp only [hc] at h1
  rw [Array.all_eq_true_iff_forall_mem] at h1
  have h2 := h1 _ (Array.mem_toList_iff.1 hcv)
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true, List.mem_range] at h2
  exact h2 i hi

/-- **`BlockPresObl`** with the block mark empty, the generated constants seen
and `ProjBodiesAll`. -/
@[expose] def BlockPresOblP : Prop :=
  EnvLaws → ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (consts : Array Lean.ConstantInfo) (nP : Nat)
    (s s' : InLean.CState) (d : ConLeche.Declaration),
    EnvPresI fe L → fe.pending = [] →
    (∀ ci ∈ consts.toList, ci ∈ InLean.storedBlock consts) →
    (∀ ci ∈ consts.toList, fe.env.find? ci.name = none) → (consts.toList.map (·.name)).Nodup →
    (∀ ci ∈ consts.toList, fe.sees ci.name ci = true) →
    consts.all InLean.constInRange = true → ProjBodiesAll consts →
    (InLean.checkIndDeclC .verified fe (InLean.storedBlock consts) nP).run s = .ok ((), s') →
    toDecl (InLean.storedBlock consts) = some d →
    let E' := consts.toList.foldl InLean.addConst fe.env
    let L' := L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d)
    (∀ c ∈ ConLeche.declConstants d, ∃ ci ∈ consts.toList, c.name = toName ci.name) ∧
    (∀ t ∈ ConLeche.declTables d, ∃ ci ∈ consts.toList, t.structName = toName ci.name) ∧
    (∀ ci ∈ consts.toList, ∃ cci, L'.find? (toName ci.name) = some cci ∧
      EntryRelI { fe with env := E' } ci cci) ∧
    (∀ ci ∈ consts.toList, TableRelI { fe with env := E' } ci.name (L'.findTable? (toName ci.name))) ∧
    (∀ t ∈ ConLeche.declTables d, (L'.find? t.structName).isSome)

/-- **An inductive block keeps the relation** (`IndGroupPresB` with the block
mark empty and InLean's `projBodiesAllOk`, which `checkInductiveC` runs). -/
@[expose] def IndGroupPresBP : Prop :=
  EnvLaws → ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (consts : Array Lean.ConstantInfo) (nP : Nat)
    (s s' : InLean.CState) (d : ConLeche.Declaration),
    EnvPresI fe L → fe.pending = [] →
    (∀ ci ∈ consts.toList, ci ∈ InLean.storedBlock consts) →
    (∀ ci ∈ consts.toList, fe.env.find? ci.name = none) → (consts.toList.map (·.name)).Nodup →
    (∀ ci ∈ consts.toList, fe.sees ci.name ci = true) →
    consts.all InLean.constInRange = true → InLean.projBodiesAllOk consts = true →
    (InLean.checkIndDeclC .verified fe (InLean.storedBlock consts) nP).run s = .ok ((), s') →
    toDecl (InLean.storedBlock consts) = some d →
    EnvPresI { fe with env := consts.foldl InLean.addConst fe.env }
      (L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d))

theorem find?_name_news {news : List ConLeche.ConstantInfo} (hnd : (news.map (·.name)).Nodup)
    {c : ConLeche.ConstantInfo} (hc : c ∈ news) :
    news.reverse.find? (·.name == c.name) = some c := by
  have h1 := find?_reverse_key (fun c : ConLeche.ConstantInfo => c.name) hnd c.name
  have h2 := find?_key (fun c : ConLeche.ConstantInfo => c.name) hnd hc
  rw [h1, h2]

/-- **The declared parameter count of an accepted recognised block** (O7's
finding 1): `toDecl` reads the record's count off the first former, and
`genEntriesAgree` checks it against the shape's, which is the declaration's
(`readBlock` sets `nP := nPd`).  So the record is at InLean's `nP`. -/
theorem toDecl_recognised {μ : CheckMode} {fe : InLean.FEnv} {block : List Lean.ConstantInfo}
    {nP : Nat} {s s' : InLean.CState} {d : ConLeche.Declaration}
    (hndB : (block.map (·.name)).Nodup) (hR : ∀ ci ∈ block, CIRange ci)
    (hrun : (InLean.checkIndDeclC μ fe block nP).run s = .ok ((), s'))
    (hd : toDecl block = some d) :
    ∃ cb, toBlock block = some cb ∧ d = .indDecl cb nP := by
  obtain ⟨-, p, hp, s₁, hgen, hks⟩ := checkIndDeclC_ok hrun
  obtain ⟨cvT0, tl, cs0, rs0, nI0, hsp', -, -, -, -⟩ := readBlock_spec hp
  obtain ⟨v0, rest, hblock, -⟩ := blockSplit_head hsp'
  have hd' := hd
  rw [hblock] at hd'
  obtain ⟨cb, htb, rfl⟩ := toDecl_ind hd'
  rw [← hblock] at htb
  obtain ⟨cvTs, cs, rs, C⟩ := recogCtx_of hndB hR cb htb hp hgen hks
  have hv0b : Lean.ConstantInfo.inductInfo v0 ∈ block := hblock ▸ List.mem_cons_self
  obtain ⟨i, hi, hiv⟩ := C.ofFormer hv0b
  obtain ⟨v', hv'b, hv'cv, -, hnP, -⟩ := C.former (List.getElem_mem hi)
  have : Lean.ConstantInfo.inductInfo v' = .inductInfo v0 :=
    C.uniq hv'b hv0b (by show v'.toConstantVal.name = v0.toConstantVal.name; rw [hv'cv, hiv])
  cases this
  exact ⟨cb, htb, by rw [hnP, C.pnP]⟩

/-- **`BlockPresObl`**, for every accepted block (a pinned basis block takes
the same route). -/
theorem blockPresOblP : BlockPresOblP := by
  intro hlaws fe L consts nP s s' d hP hpend hblk hfresh hnd hsees hrange hsteps hrun hd
  intro E' L'
  have hperm := storedBlock_perm hnd hblk
  have hmemB : ∀ ci, ci ∈ storedBlock consts ↔ ci ∈ consts.toList := fun ci => hperm.mem_iff
  have hndB : ((storedBlock consts).map (·.name)).Nodup := (hperm.map _).nodup_iff.2 hnd
  obtain ⟨-, p, hp, s₁, hgen, hks⟩ := checkIndDeclC_ok hrun
  have hR : ∀ ci ∈ storedBlock consts, CIRange ci := by
    intro ci h
    rw [Array.all_eq_true_iff_forall_mem] at hrange
    exact CIRange_of_constInRange (hrange ci (Array.mem_toList_iff.1 ((hmemB ci).1 h)))
  -- the record, at the declaration's parameter count
  obtain ⟨cb, htb, rfl⟩ := toDecl_recognised hndB hR hrun hd
  obtain ⟨cvTs, cs, rs, C⟩ := recogCtx_of hndB hR cb htb hp hgen hks
  -- con-leche's install of the record
  have hcb : cb = (storedBlock consts).map trCI := (toBlock_eq htb hR).1
  have hsh : ConLeche.readBlock nP cb = .ok (trShape p) := by
    rw [hcb]; exact readBlock_tr nP _ C.okT hp
  have hdc : ConLeche.declConstants (.indDecl cb nP) =
      ConLeche.blockConstants (trShape p) := by
    simp only [ConLeche.declConstants, hsh]
  obtain ⟨cQ, hcQ0⟩ := Option.isSome_iff_exists.1
    (cblockTables_isSome p p.members (fun ms hms c hc => by
      obtain ⟨ci, hci, hce⟩ := readBlock_ctors hp ms hms c (by rw [structCtor_ctors hc]; exact List.mem_singleton_self c)
      rw [← hce]; exact toExpr_of_okE _ (C.okT ci hci))
      (checkBlockKS_tables hks))
  have hcQ : ConLeche.blockTables (trShape p) (trShape p).members = some cQ := hcQ0
  have hdt : ConLeche.declTables (.indDecl cb nP) = cQ := by
    simp only [ConLeche.declTables, hsh]
    show (ConLeche.blockTables (trShape p) (trShape p).members).getD [] = cQ
    rw [hcQ]; rfl
  simp only [L', hdc, hdt]
  -- InLean's lookups after the group
  have hfind : ∀ ci ∈ storedBlock consts,
      ({ fe with env := E' } : InLean.FEnv).find? ci.name = some ci := by
    intro ci hci
    have hc := (hmemB ci).1 hci
    have hE := (find_foldl_addConst hlaws consts.toList fe.env hfresh hnd).1 ci hc
    rw [FEnv.find?_eq_filter]
    show (E'.find? ci.name).filter (fe.sees ci.name) = some ci
    rw [hE, Option.filter_some]; simp only [hsees ci hc, ↓reduceIte]
  -- con-leche's lookups after the group
  have hndN : ((ConLeche.blockConstants (trShape p)).map (·.name)).Nodup := by
    rw [C.news_names]
    exact List.Pairwise.map _ (fun a b hab he => hab (toName_inj he)) hndB
  have hLfind : ∀ c ∈ ConLeche.blockConstants (trShape p),
      (L.pushDelta (ConLeche.blockConstants (trShape p)) cQ).find? c.name = some c := by
    intro c hc
    rw [pushDelta_find, find?_name_news hndN hc]
  have hentry := C.entry (fe' := { fe with env := E' }) hpend hfind
  have hEntry : ∀ ci ∈ consts.toList, ∃ cci,
      (L.pushDelta (ConLeche.blockConstants (trShape p)) cQ).find? (toName ci.name) = some cci ∧
      EntryRelI { fe with env := E' } ci cci := by
    intro ci hci
    obtain ⟨cci, hcc, hn, hrel⟩ := hentry ci ((hmemB ci).2 hci)
    exact ⟨cci, hn ▸ hLfind cci hcc, hrel⟩
  obtain ⟨htn, htnd⟩ := C.tab_names
  have htabName : ∀ t ∈ cQ, ∃ ci ∈ consts.toList, t.structName = toName ci.name := by
    intro t ht
    have hm := (blockTables_names _ hcQ).subset (List.mem_map_of_mem (f := (·.structName)) ht)
    rw [htn] at hm
    obtain ⟨n, hn, hne⟩ := List.mem_map.1 hm
    obtain ⟨cvT, hcvT, rfl⟩ := List.mem_map.1 hn
    obtain ⟨w, hwb, he⟩ := blockSplit_formers C.split _ hcvT
    exact ⟨_, (hmemB _).1 hwb, by rw [← hne, ← he]; rfl⟩
  refine ⟨?_, htabName, hEntry, ?_, ?_⟩
  · intro c hc
    have hm := List.mem_map_of_mem (f := (·.name)) hc
    rw [C.news_names] at hm
    obtain ⟨n, hn, hne⟩ := List.mem_map.1 hm
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
    exact ⟨ci, (hmemB ci).1 hci, hne.symm⟩
  · intro ci hci
    obtain ⟨cci, hcf, -⟩ := hEntry ci hci
    unfold ConLeche.Env.findTable?
    rw [hcf]
    simp only [Option.isSome_some, ↓reduceIte, ConLeche.Env.pushDelta, List.find?_append]
    have hLnone : L.tables.find? (·.structName == toName ci.name) = none := by
      apply find_none_of_forall
      intro tbl ht
      cases hb : tbl.structName == toName ci.name
      · rfl
      · have h := hP.tabNames tbl ht
        rw [eq_of_beq hb, hP.none _ (by simp only [FEnv.find?_eq_filter, hfresh ci hci, Option.filter_none])] at h
        cases h
    have htnd' : (cQ.map (·.structName)).Nodup := htnd.sublist (blockTables_names _ hcQ)
    have hrev := find?_reverse_key (fun t : ConLeche.ProjTable => t.structName) htnd' (toName ci.name)
    rw [hLnone, hrev, Option.or_none]
    exact C.table (fe' := { fe with env := E' }) hpend hfind (fun v cv h1 h2 h3 => hsteps v cv ((hmemB _).1 h1) h2 ((hmemB _).1 h3))
      hcQ ci ((hmemB ci).2 hci)
  · intro t ht
    obtain ⟨ci, hci, hn⟩ := htabName t ht
    obtain ⟨cci, hcf, -⟩ := hEntry ci hci
    rw [hn, hcf]; rfl

/-- **An inductive block keeps the relation** (`IndGroupPresB` with the block
mark empty and InLean's `projBodiesAllOk`). -/
theorem indGroupPresBP : IndGroupPresBP := by
  intro hlaws fe L consts nP s s' d hP hpend hblk hfresh hnd hsees hrange hsteps hrun hd
  obtain ⟨h1, h2, h3, h4, h5⟩ := blockPresOblP hlaws fe L consts nP s s' d hP hpend hblk hfresh
    hnd hsees hrange (projBodiesAll_of_ok hsteps) hrun hd
  rw [← Array.foldl_toList]
  exact presI_group hlaws hP hfresh hnd hsees h1 h2 h3 h4 h5

end InLeanProof
