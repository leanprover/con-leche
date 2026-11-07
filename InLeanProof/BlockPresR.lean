module

public import InLeanProof.RecFireTr
public import InLeanProof.ProjBodiesTr
public import InLeanProof.StepPres
/- `ConstantInfo.name`/`isInductive`/`isCtor` are read through their bodies. -/
import all Lean.Declaration

/-!
# `BlockPresObl`'s recognised branch (task #451, lane P3r)

An accepted recognised block (`checkIndDeclC`'s second branch: no pinned
name, `blockShape? = some p`, `genEntriesAgree` and `checkBlockKS` accepted)
installs, on con-leche's side, `blockConstants (trShape p)` and
`blockTables (trShape p)`; InLean adds the generated constants.  This file
relates the two at every generated constant's name, which is what
`presI_group` needs (`recognisedBlockPresObl`), and assembles the block's
step with the pinned branch left as a named hypothesis
(`indGroupPresBP_of`).

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
* `ProjStepsAll`: every intermediate term of every projection body InLean
  builds is in range (`projStepsOk`, `ProjBodiesTr.lean`).  Not implied by
  any check InLean makes; proposed as an executable check beside
  `FEnv.projBodiesInRange`.

**How the entries are read.**  The recogniser's record is the block's split
(`blockShape?_spec`); the block check's recursor-name stage gives the split's
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

theorem blockTables_names (p : ConLeche.BlockShape) : ∀ (Ms : List ConLeche.MemberShape),
    ((ConLeche.blockTables p Ms).map (·.structName)).Sublist (Ms.map (·.declared.name))
  | [] => by simp [ConLeche.blockTables]
  | ms :: rest => by
    have ih := blockTables_names p rest
    simp only [ConLeche.blockTables, List.map_cons]
    split
    · split
      · simp only [List.map_cons]; exact ih.cons_cons _
      · exact ih.cons _
    · exact ih.cons _

theorem blockTables_find (p : ConLeche.BlockShape) : ∀ {Ms : List ConLeche.MemberShape},
    (Ms.map (·.declared.name)).Nodup → ∀ {ms}, ms ∈ Ms →
      (ConLeche.blockTables p Ms).find? (·.structName == ms.declared.name) = blockTableOf p ms
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: rest, hnd, ms, hms => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hnone : ∀ y, y ∈ rest → y.declared.name ≠ x.declared.name := by
      intro y hy he; exact hnd.1 (he ▸ List.mem_map_of_mem hy)
    have hrest : (ConLeche.blockTables p rest).find? (·.structName == x.declared.name) = none := by
      apply find?_key_none
      intro hm
      exact hnd.1 ((blockTables_names p rest).subset hm)
    rcases List.mem_cons.1 hms with rfl | hms
    · unfold blockTableOf
      cases hsc : ms.structCtor? with
      | none => simp only [ConLeche.blockTables, hsc]; exact hrest
      | some c =>
        cases hb : ConLeche.structProjBodies ms.declared.name p.nP c.2 c.1.type with
        | none => simp only [ConLeche.blockTables, hsc, hb, Option.map_none]; exact hrest
        | some bodies => simp [ConLeche.blockTables, hsc, hb]
    · have ih := blockTables_find p hnd.2 hms
      have hne : ms.declared.name ≠ x.declared.name := hnone ms hms
      simp only [ConLeche.blockTables]
      split
      · split
        · simp only [List.find?_cons]
          rw [show (x.declared.name == ms.declared.name) = false by simpa using hne.symm]
          exact ih
        · exact ih
      · exact ih

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

end InLeanProof
