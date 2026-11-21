module

public import ConLeche.IsModel
import ConLeche.Verify.Cached.IotaReadC
import ConLeche.Cached.Decls
import ConLeche.Verify.Cached.DeclPushes
public import ConLeche.Verify.Inductives.IotaRead
import ConLeche.Verify.Cached.WalkersC
import ConLeche.Verify.Cached.IndBlockC
import ConLeche.Verify.Cached.IndPositivityC
import ConLeche.Verify.Inductives.BlockShapeInv
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Driver.Copies
import ConLeche.Verify.Cached.PureRun
public import ConLeche.Kernel.CheckDecl
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Semantics.Bridge.Sound
public import ConLeche.Verify.BasisBlock

public section

/-!
# An accepted stream stores the records `IsModel` reads

`IsModel` (`ConLeche/IsModel.lean`) states one clause per record of the INPUT
(`Declaration.constants`); the proofs' model is a model of the environment the checker builds.  The
bridge between the two needs that every record of an accepted stream is stored, under its name, as
the record says (`RecordsStored`): its level parameters and type, a definition with its value, a
recursor with its rules and their firing modes, a constructor with its parameter count.

The fold pushes each declaration's `declConstants` (`checkDecls_env`) and the names are distinct
(`declsRun_chain`), so each record's constant is found under its name.  Per kind the records are the
pushed constants, except for an inductive block, read through `readBlock`:

* a type former is pushed as declared (`readBlock_declared`);
* a recursor is pushed with its rules, each with the firing mode `recFire` computes (which the
  statement does not read: `StoredAs` compares rules up to it, `RecRule.unfired`);
* a constructor is pushed in the group of the member its result names (`blockGroups`); at two or
  more members a constructor in no group is not pushed, and the recursor check's pin
  (`targetRecPins`, "constructor grouping") rejects that block: an accepted block's grouped
  constructors are its constructors, by name (`checkDeclStepC_blockRead`).
-/

namespace ConLeche

/-- A rule without its firing mode (the install computes it; the statement reads none). -/
@[expose] def RecRule.unfired (rl : RecRule) : RecRule := { rl with fire := .plain }

/-- **`ci` stores the record `c`**: the same level parameters and type, a definition with its value,
a recursor with its rules (up to their firing modes), a constructor with its parameter count. -/
@[expose] def StoredAs (ci c : ConstantInfo) : Prop :=
  ci.toConstantVal = c.toConstantVal ∧
  (∀ cv v h, c = .defnInfo cv v h → ci = c) ∧
  (∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules →
    ∃ isK' rules', ci = .recInfo cv mI rP isK' rules' ∧
      rules'.map RecRule.unfired = rules.map RecRule.unfired) ∧
  (∀ cvj cnP nF T, c = .ctorInfo cvj cnP nF T → ∃ nF' T', ci = .ctorInfo cvj cnP nF' T')

/-- **A constant, a stored one at other level-parameter names**: its statement (and a
definition's value) the stored constant's instantiated at its own level parameters, as many, neither
list with a repeat; a recursor or a constructor never (a block is matched as it is). -/
@[expose] def RenamedAs (ci c : ConstantInfo) : Prop :=
  ci.toConstantVal.levelParams.Nodup ∧ c.toConstantVal.levelParams.Nodup ∧
  ci.toConstantVal.levelParams.length = c.toConstantVal.levelParams.length ∧
  c.name = ci.name ∧
  c.toConstantVal.type = ci.toConstantVal.type.instantiateLevelParams
    ci.toConstantVal.levelParams (c.toConstantVal.levelParams.map Level.param) ∧
  (∀ cv v h, c = .defnInfo cv v h → ∃ cv' v', ci = .defnInfo cv' v' h ∧
    v = v'.instantiateLevelParams ci.toConstantVal.levelParams
      (c.toConstantVal.levelParams.map Level.param)) ∧
  (∀ cv mI rP isK rules, c ≠ .recInfo cv mI rP isK rules) ∧
  (∀ cvj cnP nF T, c ≠ .ctorInfo cvj cnP nF T)

/-- A record of a stream is a record of one of its declarations. -/
theorem mem_constantsOf {ds : List Declaration} {c : ConstantInfo} :
    c ∈ constantsOf ds ↔ ∃ d ∈ ds, c ∈ d.constants := List.mem_flatMap

/-- **A model of a set of constants is a model of every subset.** -/
theorem IsModel.anti {V : Type w} [SetTheory V] {model : Name → List Nat → V}
    {C C' : ConstantInfo → Prop} (h : IsModel V model C) (hsub : ∀ c, C' c → C c) :
    IsModel V model C' :=
  fun c hc => h c (hsub c hc)

/-- **Every record of the input is stored** under its name (`StoredAs`), a recursor's as one
reading its ι equations off its own type (`RecReads`, the checker's rule) or as a quotient
constant. -/
@[expose] def RecordsStored (R : ConstantInfo → Prop) (env : Env) : Prop :=
  ∀ c, R c → ∃ ci, env.find? c.name = some ci ∧ StoredAs ci c ∧
    ∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules →
      RecReads env.find? ci ∨ ∃ k cv, ci = quotAt k cv

theorem StoredAs.refl (c : ConstantInfo) : StoredAs c c :=
  ⟨rfl, fun _ _ _ _ => rfl, fun _ _ _ isK rules h => ⟨isK, rules, h, rfl⟩,
    fun _ _ nF T h => ⟨nF, T, h⟩⟩

theorem StoredAs.trans {a b c : ConstantInfo} (hab : StoredAs a b) (hbc : StoredAs b c) :
    StoredAs a c := by
  obtain ⟨a1, a2, a3, a4⟩ := hab
  obtain ⟨b1, b2, b3, b4⟩ := hbc
  refine ⟨a1.trans b1, fun cv v h hc => ?_, fun cv mI rP isK rules hc => ?_,
    fun cvj cnP nF T hc => ?_⟩
  · rw [a2 cv v h ((b2 cv v h hc).trans hc), b2 cv v h hc]
  · obtain ⟨isK', rules', hb, hr⟩ := b3 cv mI rP isK rules hc
    obtain ⟨isK'', rules'', ha, hr'⟩ := a3 cv mI rP isK' rules' hb
    exact ⟨isK'', rules'', ha, hr'.trans hr⟩
  · obtain ⟨nF', T', hb⟩ := b4 cvj cnP nF T hc
    obtain ⟨nF'', T'', ha⟩ := a4 cvj cnP nF' T' hb
    exact ⟨nF'', T'', ha⟩

/-- Fewer records are stored where more are. -/
theorem RecordsStored.mono {R R' : ConstantInfo → Prop} {env : Env} (h : RecordsStored R' env)
    (hsub : ∀ c, R c → ∃ c', R' c' ∧ StoredAs c' c) : RecordsStored R env := by
  intro c hc
  obtain ⟨c', hc', hst⟩ := hsub c hc
  obtain ⟨ci, hf, hci, hr⟩ := h c' hc'
  have hn : c'.name = c.name := congrArg ConstantVal.name hst.1
  refine ⟨ci, hn ▸ hf, hci.trans hst, fun cv mI rP isK rules hc1 => ?_⟩
  obtain ⟨isK', rules', h', -⟩ := hst.2.2.1 cv mI rP isK rules hc1
  exact hr cv mI rP isK' rules' h'

/-! ## The block's records -/

/-- What `blockSplit` splits: every record of the block is one of its formers, constructors or
recursors. -/
theorem mem_of_blockSplitRecs :
    ∀ {block : List ConstantInfo} {rs : List (ConstantVal × Nat × Nat × Bool × List RecRule)},
      blockSplitRecs block = some rs → ∀ b ∈ block,
        ∃ cv mI rP isK rules, b = .recInfo cv mI rP isK rules ∧ (cv, mI, rP, isK, rules) ∈ rs
  | [], _, _, b, hb => nomatch hb
  | .recInfo cvR mI rP isK rules :: rest, rs, h, b, hb => by
    simp only [blockSplitRecs, Option.map_eq_some_iff] at h
    obtain ⟨rs', h', rfl⟩ := h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, _, _, _, _, rfl, List.mem_cons_self⟩
    · obtain ⟨cv, mI', rP', isK', rules', rfl, hm⟩ := mem_of_blockSplitRecs h' b hb
      exact ⟨_, _, _, _, _, rfl, List.mem_cons_of_mem _ hm⟩
  | .axiomInfo .. :: _, _, h, _, _ | .defnInfo .. :: _, _, h, _, _ | .thmInfo .. :: _, _, h, _, _
  | .indInfo .. :: _, _, h, _, _ | .ctorInfo .. :: _, _, h, _, _ => nomatch h

theorem mem_of_blockSplitCtors :
    ∀ {block : List ConstantInfo} {cs : List (ConstantVal × Nat × Nat)}
      {rs : List (ConstantVal × Nat × Nat × Bool × List RecRule)},
      blockSplitCtors block = some (cs, rs) → ∀ b ∈ block,
        (∃ cv nP nF T, b = .ctorInfo cv nP nF T ∧ (cv, nP, nF) ∈ cs) ∨
        (∃ cv mI rP isK rules, b = .recInfo cv mI rP isK rules ∧ (cv, mI, rP, isK, rules) ∈ rs)
  | .ctorInfo cvC nP nF T :: rest, cs, rs, h, b, hb => by
    simp only [blockSplitCtors, Option.map_eq_some_iff] at h
    obtain ⟨⟨cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases List.mem_cons.mp hb with rfl | hb
    · exact .inl ⟨_, _, _, _, rfl, List.mem_cons_self⟩
    · rcases mem_of_blockSplitCtors h' b hb with ⟨cv, nP', nF', T', rfl, hm⟩ | hr
      · exact .inl ⟨_, _, _, _, rfl, List.mem_cons_of_mem _ hm⟩
      · exact .inr hr
  | [], cs, rs, h, b, hb | .recInfo .. :: _, cs, rs, h, b, hb | .axiomInfo .. :: _, cs, rs, h, b, hb
  | .defnInfo .. :: _, cs, rs, h, b, hb | .thmInfo .. :: _, cs, rs, h, b, hb
  | .indInfo .. :: _, cs, rs, h, b, hb => by
    simp only [blockSplitCtors] at h
    obtain ⟨rs', h', he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact .inr (mem_of_blockSplitRecs h' b hb)

theorem mem_of_blockSplit :
    ∀ {block : List ConstantInfo} {cvTs : List ConstantVal} {cs : List (ConstantVal × Nat × Nat)}
      {rs : List (ConstantVal × Nat × Nat × Bool × List RecRule)},
      blockSplit block = some (cvTs, cs, rs) → ∀ b ∈ block,
        (∃ cv caps, b = .indInfo cv caps ∧ cv ∈ cvTs) ∨
        (∃ cv nP nF T, b = .ctorInfo cv nP nF T ∧ (cv, nP, nF) ∈ cs) ∨
        (∃ cv mI rP isK rules, b = .recInfo cv mI rP isK rules ∧ (cv, mI, rP, isK, rules) ∈ rs)
  | .indInfo cvT caps :: rest, cvTs, cs, rs, h, b, hb => by
    simp only [blockSplit, Option.map_eq_some_iff] at h
    obtain ⟨⟨cvTs', cs', rs'⟩, h', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    rcases List.mem_cons.mp hb with rfl | hb
    · exact .inl ⟨_, _, rfl, List.mem_cons_self⟩
    · rcases mem_of_blockSplit h' b hb with ⟨cv, caps', rfl, hm⟩ | hr
      · exact .inl ⟨_, _, rfl, List.mem_cons_of_mem _ hm⟩
      · exact .inr hr
  | [], cvTs, cs, rs, h, b, hb | .recInfo .. :: _, cvTs, cs, rs, h, b, hb
  | .axiomInfo .. :: _, cvTs, cs, rs, h, b, hb | .defnInfo .. :: _, cvTs, cs, rs, h, b, hb
  | .thmInfo .. :: _, cvTs, cs, rs, h, b, hb | .ctorInfo .. :: _, cvTs, cs, rs, h, b, hb => by
    simp only [blockSplit] at h
    obtain ⟨⟨cs', rs'⟩, h', he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact .inr (mem_of_blockSplitCtors h' b hb)

theorem mem_blockRecs (p : BlockShape) {rc : RecShape} :
    ∀ {l : List RecShape}, rc ∈ l →
      ConstantInfo.recInfo rc.cvR rc.mI rc.rP rc.isK
        (rc.rules.map ({ · with fire := recFire p rc })) ∈ blockRecs p l
  | _ :: _, .head _ => List.mem_cons_self
  | _ :: _, .tail _ h => List.mem_cons_of_mem _ (mem_blockRecs p h)

theorem inj_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: l, hnd, a, b, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · rw [h1, h2]
    · subst h1; exact absurd (he ▸ List.mem_map_of_mem h2) hnd.1
    · subst h2; exact absurd (he.symm ▸ List.mem_map_of_mem h1) hnd.1
    · exact inj_of_nodup_map hnd.2 h1 h2 he

/-- What an accepted block's step established of its records: it reads, its grouped
constructors are distinct by name, and they are its constructors, by name. -/
@[expose] def BlockRead (nP : Nat) (block : List ConstantInfo) : Prop :=
  ∃ p, readBlock nP block = .ok p ∧ (p.allCtors.map (·.1.name)).Nodup ∧
    ∀ cvTs cs rs, blockSplit block = some (cvTs, cs, rs) →
      p.allCtors.map (·.1.name) = cs.map (·.1.name)

/-- **A read block's records are stored** among its constants. -/
theorem blockRecords_stored {nP : Nat} {block : List ConstantInfo} (h : BlockRead nP block) :
    ∀ c ∈ block, ∃ ci ∈ declConstants (.indDecl block nP), StoredAs ci c := by
  obtain ⟨p, hp, hnd, hg⟩ := h
  have hd := readBlock_declared hp
  obtain ⟨-, -, -, -, -, -, -, cvTs, cs, rs, nIdxs, hsp, hk, -, hnl, -, hcsP, hmem, hrecs⟩ :=
    readBlock_inv hp
  have hDC : declConstants (.indDecl block nP) = blockConstants p := by
    simp only [declConstants, hp]
  rw [hDC]
  have hgrp := hg cvTs cs rs hsp
  -- the members, read back
  obtain ⟨e1, -, e3⟩ := blockMembers_proj (cvTs := cvTs) (nIdxs := nIdxs)
    (groups := blockGroups p.memberNames p.lps p.nP p.k (cs.map fun c => (c.1, c.2.2)))
    (by rw [hnl, hk]) (by rw [blockGroups_length, hk])
  rw [← hmem] at e1 e3
  have hnames : p.memberNames = cvTs.map (·.name) := by
    rw [BlockShape.memberNames, ← e1, List.map_map]; rfl
  intro b hb
  rcases mem_of_blockSplit hsp b hb with ⟨cv, caps, rfl, hcv⟩ | ⟨cv, nP', nF, T, rfl, hcv⟩ |
    ⟨cv, mI, rP, isK, rules, rfl, hcv⟩
  · -- a type former: pushed as declared
    have hdecl : p.members.map (·.declared) = cvTs := by
      rw [← e1]; exact List.map_congr_left fun m hm => hd m hm
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcv
    refine ⟨.indInfo cv (blockCapsAt p i (blockIsRec p)), ?_, ⟨rfl, ?_, ?_, ?_⟩⟩
    · unfold blockConstants blockFormers
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      refine List.mem_map.mpr ⟨(cv, i), ?_, rfl⟩
      rw [List.mem_zipIdx_iff_getElem?, hdecl]
      simpa using hi
    · intro _ _ _ h; exact nomatch h
    · intro _ _ _ _ _ h; exact nomatch h
    · intro _ _ _ _ h; exact nomatch h
  · -- a constructor: pushed in its member's group
    have hcn : cv.name ∈ p.allCtors.map (·.1.name) := by
      rw [hgrp]; exact List.mem_map.mpr ⟨_, hcv, rfl⟩
    obtain ⟨a, ha, han⟩ := List.mem_map.mp hcn
    obtain ⟨g, hg', hag⟩ := List.mem_flatten.mp ha
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hg'
    have hmsg : ms.ctors ∈ blockGroups p.memberNames p.lps p.nP p.k
        (cs.map fun c => (c.1, c.2.2)) := by
      rw [← e3]; exact List.mem_map_of_mem hms
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (mem_blockGroups hmsg hag)
    have hndcs : (cs.map (·.1.name)).Nodup := hgrp ▸ hnd
    have hc'eq : c' = (cv, nP', nF) := inj_of_nodup_map hndcs hc' hcv han
    subst hc'eq
    refine ⟨.ctorInfo cv p.nP nF ms.cvT.name, ?_, ⟨rfl, ?_, ?_, ?_⟩⟩
    · unfold blockConstants blockCtors
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      refine List.mem_flatMap.mpr ⟨(ms.cvT.name, ms.ctors), ?_, ?_⟩
      · exact List.mem_map.mpr ⟨ms, hms, rfl⟩
      · exact List.mem_map.mpr ⟨_, hag, rfl⟩
    · intro _ _ _ h; exact nomatch h
    · intro _ _ _ _ _ h; exact nomatch h
    · intro cvj cnP nF' T' h
      injection h with h1 h2
      subst h1 h2
      have hn := hcsP _ hcv
      simp only at hn
      exact ⟨nF, ms.cvT.name, by rw [hn]⟩
  · -- a recursor: pushed with its rules, each with its firing mode
    have hrc : (⟨cv, rP, mI, recTargetOf p.memberNames mI cv.type, rules, isK⟩ : RecShape)
        ∈ p.recs := by
      rw [hrecs]; exact List.mem_map.mpr ⟨_, hcv, rfl⟩
    refine ⟨_, List.mem_append_right _ (mem_blockRecs p hrc), ⟨rfl, ?_, ?_, ?_⟩⟩
    · intro _ _ _ h; exact nomatch h
    · intro cv' mI' rP' isK' rules' h
      simp only [ConstantInfo.recInfo.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      refine ⟨isK, _, rfl, ?_⟩
      simp only [List.map_map]
      rfl
    · intro _ _ _ _ h; exact nomatch h

/-- **A declaration's records are stored** among its constants, given that a block reads. -/
theorem records_stored {d : Declaration}
    (hb : ∀ block nP, d = .indDecl block nP → BlockRead nP block) :
    ∀ c ∈ d.constants, ∃ ci ∈ declConstants d, StoredAs ci c := by
  intro c hc
  cases d with
  | axiomDecl cv =>
    refine ⟨c, ?_, StoredAs.refl c⟩
    simp only [Declaration.constants] at hc
    simp only [declConstants]
    exact hc
  | defnDecl cv v hint =>
    refine ⟨.defnInfo cv v hint, List.mem_singleton_self _, ?_⟩
    simp only [Declaration.constants] at hc
    split at hc
    · obtain rfl := List.mem_singleton.mp hc
      refine ⟨rfl, ?_, ?_, ?_⟩
      · intro _ _ _ h; exact nomatch h
      · intro _ _ _ _ _ h; exact nomatch h
      · intro _ _ _ _ h; exact nomatch h
    · obtain rfl := List.mem_singleton.mp hc
      exact StoredAs.refl _
  | thmDecl cv v =>
    obtain rfl := List.mem_singleton.mp hc
    exact ⟨_, List.mem_singleton_self _, StoredAs.refl _⟩
  | opaqueDecl cv v =>
    obtain rfl := List.mem_singleton.mp hc
    exact ⟨_, List.mem_singleton_self _, StoredAs.refl _⟩
  | quotDecl k cv =>
    obtain rfl := List.mem_singleton.mp hc
    exact ⟨_, List.mem_singleton_self _, StoredAs.refl _⟩
  | indDecl block nP => exact blockRecords_stored (hb block nP rfl) c hc

end ConLeche

/-! ## What an accepted step establishes of a block -/

namespace ConLeche.Cached

open ConLeche

/-- The recursor check's grouping pin, as a postcondition. -/
theorem genRecCheckC_grouping (mode : CheckMode) (fe : FEnv)
    (p : BlockShape) (nestedBit : Bool) (params : List Expr) (tbl : List NestCtorNf)
    (rd : ClassRead) (Ms₀ : List TargetMajor) (block : List ConstantInfo) :
    Yields (genRecCheckC mode fe p nestedBit params tbl rd Ms₀ block)
      (fun _ => ∀ cvTs cs rs, blockSplit block = some (cvTs, cs, rs) →
        p.allCtors.map (·.1.name) = cs.map (·.1.name)) := by
  unfold genRecCheckC
  refine Yields.bind' (Q := fun _ => ∀ cvTs cs rs, blockSplit block = some (cvTs, cs, rs) →
    p.allCtors.map (·.1.name) = cs.map (·.1.name)) ?_ fun _ h => Yields.const h
  unfold targetRecPins
  dsimp only
  by_cases h1 : blockRecLpsOk p = true
  case neg => rw [ite_eq_right h1]; exact Yields.ofThrow
  rw [ite_eq_left h1]
  by_cases h2 : blockRecNamesUnreserved p = true
  case neg => rw [ite_eq_right h2]; exact Yields.ofThrow
  rw [ite_eq_left h2]
  split
  case isFalse => exact Yields.ofThrow
  split
  case isFalse => exact Yields.ofThrow
  by_cases h5 : (p.recs.map (·.cvR.name)).Nodup
  case neg => rw [ite_eq_right h5]; exact Yields.ofThrow
  rw [ite_eq_left h5]
  split
  · next cvTs cs rs hs =>
    split
    · next hc =>
      refine Yields.pure fun cvTs' cs' rs' hs' => ?_
      rw [hs] at hs'
      simp only [Option.some.injEq, Prod.mk.injEq] at hs'
      obtain ⟨rfl, rfl, rfl⟩ := hs'
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact hc.2
    · exact Yields.ofThrow
  · exact Yields.ofThrow

/-- A block pass keeps the members. -/
theorem checkBlockPassS_members (mode : CheckMode) (fe : FEnv) (p₀ : BlockShape) (isRec : Bool) :
    Yields (checkBlockPassS mode fe p₀ isRec) (fun r => r.p.members = p₀.members) := by
  unfold checkBlockPassS
  simp only [checkBlockClassesC_eq, blockNestCtxC_eq, checkBlockPositivityC_eq, nestSeedsC_eq,
    classSeedsC_eq]
  refine Yields.bind' (checkBlockIndsC_fresh mode fe p₀ isRec) fun r₁ h₁ => ?_
  obtain ⟨fe₁, p₁⟩ := r₁
  obtain ⟨⟨s, hps⟩, -, -⟩ := h₁
  try simp only [] at hps
  subst hps
  yields
  all_goals exact Yields.pure (BlockShape.withSort_members p₀ s)

theorem checkBlockTailS_grouping (mode : CheckMode) {block : List ConstantInfo}
    {q : BlockPass FEnv} {Q : List ProjTable} :
    Yields (checkBlockTailS mode block q Q) (fun _ =>
      ∀ cvTs cs rs, blockSplit block = some (cvTs, cs, rs) →
        q.p.allCtors.map (·.1.name) = cs.map (·.1.name)) := by
  obtain ⟨env₁, p, kinds, params, rd, cls, tbl⟩ := q
  unfold checkBlockTailS
  dsimp only
  refine Yields.bind fun _ => ?_
  refine Yields.bind fun _ => ?_
  exact Yields.bind' (genRecCheckC_grouping mode _ p _ _ _ _ _ block) fun _ h => Yields.const h

/-- **An accepted block's grouping**: its grouped constructors are distinct and are its
constructors, by name. -/
theorem checkBlockKS_grouping (mode : CheckMode) (fe : FEnv) (block : List ConstantInfo)
    (p : BlockShape) (hd : ∀ ms ∈ p.members, ms.declared = ms.cvT) :
    Yields (checkBlockKS mode fe block p) (fun _ => (p.allCtors.map (·.1.name)).Nodup ∧
      ∀ cvTs cs rs, blockSplit block = some (cvTs, cs, rs) →
        p.allCtors.map (·.1.name) = cs.map (·.1.name)) := by
  unfold checkBlockKS
  rw [blockTablesC_eq, blockIsRecC_eq, blockConstantsC_eq]
  try apply Yields.letFun
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun hnd => ?nb)
  case nb =>
  refine Yields.ofDecCases (fun _ => Yields.ofThrowBind) (fun _ => ?main)
  case main =>
  refine Yields.bind' (reduceMembersS_same mode fe p.nP p.members) fun ms hms => ?_
  ybind
  obtain ⟨-, -, e₃⟩ := sameMembers_names hms hd
  refine Yields.bind' (checkBlockPassS_members mode fe { p with members := ms } (blockIsRec p))
    fun q hq => ?_
  refine Yields.bind' Yields.unwrapOr fun Q _ => ?_
  refine Yields.bind' (checkBlockTailS_grouping mode) fun _ hg => Yields.pure ⟨hnd.1, ?_⟩
  intro cvTs cs rs hs
  rw [← hg cvTs cs rs hs]
  show ((p.members.map (·.ctors)).flatten).map _ = ((q.p.members.map (·.ctors)).flatten).map _
  rw [hq]
  show _ = ((ms.map (·.ctors)).flatten).map _
  rw [e₃]

/-- **An accepted block step read its block** (`BlockRead`). -/
theorem checkDeclStepC_blockRead (mode : CheckMode) (pins : List NatOpPinSet) (fe : FEnv)
    (block : List ConstantInfo) (nP : Nat) :
    Yields (checkDeclStepC mode pins fe (.indDecl block nP)) (fun _ => BlockRead nP block) := by
  unfold checkDeclStepC
  ybind
  unfold checkDeclC
  refine Yields.bind' (Q := fun _ => BlockRead nP block) ?_ fun _ h => ?_
  · unfold checkDeclKindC
    simp only []
    unfold checkIndDeclC
    split
    · cases hbp : readBlock nP block with
      | error e => exact Yields.ofThrow
      | ok p =>
        refine Yields.bind' (checkBlockKS_grouping mode _ block p (readBlock_declared hbp))
          fun _ h => ?_
        split
        · exact Yields.pure ⟨p, hbp, h⟩
        · exact Yields.ofThrow
    · exact Yields.ofThrow
  · yields
    all_goals exact Yields.pure h

/-- Every block of an accepting run read. -/
theorem declsRun_blockRead {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {J : Option Solution} {ds : List Declaration} {p q : Nat × FEnv}
    (h : DeclsRun mode pins maxNatSize J ds p q) :
    ∀ d ∈ ds, ∀ block nP, d = .indDecl block nP → BlockRead nP block := by
  induction h with
  | nil => intro _ h; exact nomatch h
  | @cons pd ds p p₁ q hstep rest ih =>
    intro d hd block nP hdb
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨fe₁, s₁, -, hC⟩ := declStep_ok hstep
      subst hdb
      rw [checkRecordC_own mode J _ rfl] at hC
      exact checkDeclStepC_blockRead mode pins _ block nP _ fe₁ s₁ hC
    · exact ih d hd block nP hdb

/-- **An accepted pure block step read its block** (`BlockRead`): its run (`BlockRun`) holds
the grouped constructors distinct, and the recursors' pins their grouping. -/
theorem checkDecl_blockRead {pins : List NatOpPinSet} {F : Nat} {env env' : Env}
    {block : List ConstantInfo} {nP : Nat}
    (h : checkDecl .verified (fueledOps .verified F) pins env (.indDecl block nP) = .ok env') :
    BlockRead nP block := by
  obtain ⟨-, hrun⟩ := Semantics.checkDeclRun_ofEnvFactsK h
  simp only [Semantics.DeclKindRun, Semantics.DeclIndRunDispatchK] at hrun
  cases hbp : readBlock nP block with
  | error e => simp only [hbp] at hrun
  | ok p₀ =>
    simp only [hbp] at hrun
    have hd := readBlock_declared hbp
    obtain ⟨ms, hms, -, -, hndC, -, -, isRec, env₁, p₁, sortsss, ctx, holes, rd, Ms,
      kinds, nfs, pos, st, isorts, out, -, hInd, -, -, -, -, -, -, -, hRec, -, -, -, -, -⟩ := hrun
    obtain ⟨-, -, -, -, hctors⟩ := reduceMembers_inv hd hms
    obtain ⟨-, -, -, s0, -, -, hp1, -⟩ := checkBlockInds_shape hInd
    subst hp1
    have hNC : ({ p₀ with members := ms } : BlockShape).allCtors = p₀.allCtors := by
      show (ms.map (·.ctors)).flatten = (p₀.members.map (·.ctors)).flatten
      rw [hctors]
    unfold checkBlockRec at hRec
    obtain ⟨R⟩ := genRecCheck_run hRec
    have hg := targetRecPins_grouping R.pins
    simp only [BlockShape.withSort_allCtors, hNC] at hg
    exact ⟨p₀, hbp, by rw [← hNC]; exact hndC, hg⟩

/-- **Every block of a pure run read.** -/
theorem _root_.ConLeche.PureRun.blockRead {pins : List NatOpPinSet} {ds : List Declaration}
    {E E' : Env} (h : PureRun pins ds E E') :
    ∀ d ∈ ds, ∀ block nP, d = .indDecl block nP → BlockRead nP block := by
  induction h with
  | nil => intro _ h; exact nomatch h
  | cons hs _ ih =>
    intro d hd block nP hdb
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨F, hF⟩ := hs
      subst hdb
      exact checkDecl_blockRead hF
    · exact ih d hd block nP hdb

/-- **An accepted block step applied the ι reading rule** (`blockReadsOk`) at its output. -/
theorem checkDeclStepC_reads (mode : CheckMode) (pins : List NatOpPinSet) (fe : FEnv)
    (block : List ConstantInfo) (nP : Nat) :
    Yields (checkDeclStepC mode pins fe (.indDecl block nP))
      (fun fe' => ∀ p, readBlock nP block = .ok p → blockReadsOk fe'.find? p = .ok ()) := by
  unfold checkDeclStepC
  ybind
  unfold checkDeclC
  refine Yields.bind' (Q := fun fe' => ∀ p, readBlock nP block = .ok p →
    blockReadsOk fe'.find? p = .ok ()) ?_ fun _ h => ?_
  · unfold checkDeclKindC
    simp only []
    unfold checkIndDeclC
    split
    · cases hbp : readBlock nP block with
      | error e => exact Yields.ofThrow
      | ok p =>
        refine Yields.bind fun fe' => ?_
        split
        · next u hu =>
          refine Yields.pure fun p' hp' => ?_
          cases hp'
          cases u
          rw [← blockReadsOkC_eq]
          exact hu
        · exact Yields.ofThrow
    · exact Yields.ofThrow
  · yields
    all_goals exact Yields.pure h

/-- **Every recursor an accepting run installs reads** at the run's end, or is a quotient
constant. -/
theorem declsRun_reads {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {J : Option Solution} {ds : List Declaration} {p q : Nat × FEnv}
    (h : DeclsRun mode pins maxNatSize J ds p q) {env₀ : Env} (hc : PushChain env₀ p.2) :
    ∀ d ∈ ds, ∀ ci ∈ declConstants d, RecReads q.2.env.find? ci ∨ ∃ k cv, ci = quotAt k cv := by
  induction h with
  | nil => intro _ h; exact nomatch h
  | @cons pd ds p p₁ q hstep rest ih =>
    obtain ⟨fe₁, s₁, rfl, hC⟩ := declStep_ok hstep
    have hc₁ : PushChain env₀ fe₁ := checkRecordC_push mode J hc pd _ fe₁ s₁ hC
    have hq : PushChain fe₁.env q.2 := declsRun_chain mode rest (PushChain.self hc₁.canon)
    intro d hd ci hci
    rcases List.mem_cons.mp hd with rfl | hd
    · cases d with
      | indDecl block nP =>
        simp only [declConstants] at hci
        split at hci
        · next p' hp' =>
          left
          intro cv mI rP isK rules hcr
          rw [checkRecordC_own mode J _ rfl] at hC
          have hR := blockReadsOk_reads
            (checkDeclStepC_reads mode pins _ block nP _ fe₁ s₁ hC p' hp') ci
            (blockConstants_rec hci hcr)
          rw [show fe₁.find? = fe₁.env.find? from funext hc₁.find?] at hR
          exact RecReads.mono (fun n c h => PushChain.find?_some hq h) hR cv mI rP isK rules hcr
        · exact nomatch hci
      | quotDecl k cv =>
        simp only [declConstants, List.mem_singleton] at hci
        exact .inr ⟨k, cv, hci⟩
      | axiomDecl cv =>
        left; intro _ _ _ _ _ hcr
        simp only [declConstants] at hci
        split at hci
        · rw [List.mem_singleton] at hci; subst hci
          simp [quotAt, quotPin, BasisKind.decls, quotBasis, quotSoundA, QuotKind.slot,
            ConstantInfo.atLps] at hcr
        · split at hci
          · exact nomatch hci
          · rw [List.mem_singleton] at hci; subst hci; exact nomatch hcr
      | defnDecl | thmDecl | opaqueDecl =>
        left; intro _ _ _ _ _ hcr
        simp only [declConstants, List.mem_singleton] at hci
        subst hci; exact nomatch hcr
    · exact ih hc₁ d hd ci hci

/-- **An accepting run stores its records** (`RecordsStored`). -/
theorem declsRun_recordsStored {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {J : Option Solution} {ds : List Declaration} {n : Nat} {fe : FEnv}
    (run : DeclsRun mode pins maxNatSize J ds (0, mkFEnv Env.empty) (n, fe)) :
    RecordsStored (· ∈ constantsOf ds) fe.env := by
  have henv : fe.env = streamEnv ds := declsRun_env mode run
  have hnd : NodupNames fe.env :=
    (declsRun_chain mode run (PushChain.refl Env.empty)).2.2.1 List.nodup_nil
  have hb := declsRun_blockRead run
  have hr := declsRun_reads run (PushChain.refl Env.empty)
  intro c hc
  obtain ⟨d, hd, hc⟩ := mem_constantsOf.1 hc
  obtain ⟨ci, hci, hst⟩ := records_stored (hb d hd) c hc
  have hmem : ci ∈ fe.env.consts := by
    rw [henv]
    exact (Driver.mem_streamEnv_consts ds _).2 (.inl ⟨d, hd, hci⟩)
  have hn : c.name = ci.name := by
    show c.toConstantVal.name = ci.toConstantVal.name
    rw [hst.1]
  exact ⟨ci, hn ▸ Driver.find?_of_nodup hnd hmem, hst, fun _ _ _ _ _ _ => hr d hd ci hci⟩

/-- **An accepted stream stores its records** (`RecordsStored`), the records the fold read (with
a solution, `sideRecords`). -/
theorem checkDecls_recordsStored {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {ds : Array Declaration} {justify : Option Env} {env : Env}
    (h : checkDeclsWith mode pins maxNatSize ds justify = .ok env) :
    RecordsStored (· ∈ constantsOf (sideRecords justify ds).toList) env := by
  obtain ⟨n, fe, run, rfl⟩ := checkDecls_run mode h
  exact declsRun_recordsStored run

/-! ## The pinned blocks an accepted stream declares -/

/-- **An accepted record passed the reserved names' check** (`basisNamesOk`, after the
record's own checks). -/
theorem checkDeclStepC_basisNamesOk {mode : CheckMode} {pins : List NatOpPinSet} {fe : FEnv}
    {d : Declaration} {s : CState} {r : FEnv × CState}
    (h : checkDeclStepC mode pins fe d s = .ok r) : basisNamesOk d = true := by
  have hY : Yields (checkDeclStepC mode pins fe d) (fun _ => basisNamesOk d = true) := by
    unfold checkDeclStepC
    ybind
    unfold checkDeclC
    ybind
    by_cases hb : basisNamesOk d = true
    · exact Yields.const hb
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact Yields.ofThrowBind
  exact hY s r.1 r.2 h

/-- Every record of an accepting run passed the reserved names' check. -/
theorem declsRun_basisNamesOk {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {J : Option Solution} {ds : List Declaration} {p q : Nat × FEnv}
    (h : DeclsRun mode pins maxNatSize J ds p q) :
    ∀ d ∈ ds, basisNamesOk d = true := by
  induction h with
  | nil => intro _ h; exact nomatch h
  | @cons pd ds p p₁ q hstep rest ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨fe₁, s₁, -, hC⟩ := declStep_ok hstep
      refine checkRecordC_yields mode J p.2 d (P := fun _ => basisNamesOk d = true)
        (fun s r s' h => checkDeclStepC_basisNamesOk (r := (r, s')) h) (fun J' cv hJ hj => ?_)
        _ _ _ hC
      subst hJ
      unfold checkRecordC
      simp only [hj]
      refine Yields.bind fun _ => ?_
      cases justifyWhy J' p.2 cv with
      | some why => exact Yields.ofThrowBind
      | none =>
        refine Yields.bind fun _ => ?_
        by_cases hb : basisNamesOk d = true
        · exact Yields.const hb
        · simp only [hb, Bool.false_eq_true, ↓reduceIte]
          exact Yields.ofThrowBind
    · exact ih d hd

/-- The four pinned inductive blocks. -/
@[expose] def pinnedKinds : List BasisKind := [.eqK, .natK, .emptyK, .falseK]

/-- A block the fold reads with a solution is the input's. -/
theorem mem_sideRecords_ind {j : Option Env} {ds : Array Declaration}
    {block : List ConstantInfo} {nP : Nat}
    (h : Declaration.indDecl block nP ∈ (sideRecords j ds).toList) :
    Declaration.indDecl block nP ∈ ds.toList := by
  cases j with
  | none => exact h
  | some e =>
    simp only [sideRecords, Array.toList_map, List.mem_map] at h
    obtain ⟨d, hd, he⟩ := h
    cases d with
    | indDecl b n => simp only [sideRecord] at he; rw [← he]; exact hd
    | defnDecl _ _ _ => simp only [sideRecord] at he; split at he <;> cases he
    | thmDecl _ _ => simp only [sideRecord] at he; split at he <;> cases he
    | opaqueDecl _ _ => simp only [sideRecord] at he; split at he <;> cases he
    | axiomDecl _ => simp only [sideRecord] at he; cases he
    | quotDecl _ _ => simp only [sideRecord] at he; cases he

/-- **A pinned block's name, stored by an accepted stream, is that block's**: the stream holds a
block that is the pin up to its level-parameter names. -/
theorem checkDecls_pinned {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {ds : Array Declaration} {justify : Option Env} {env : Env}
    (h : checkDeclsWith mode pins maxNatSize ds justify = .ok env)
    {kind : BasisKind} (hk : kind ∈ pinnedKinds) {n : Name} (hn : n ∈ kind.decls.map (·.name))
    (hs : (env.find? n).isSome = true) :
    ∃ block nP, Declaration.indDecl block nP ∈ ds.toList ∧
      listBeqBy pinCopyOk block kind.decls = true := by
  have henv := checkDecls_env h
  obtain ⟨n', fe, run, -⟩ := checkDecls_run mode h
  have hbn := declsRun_basisNamesOk run
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hs
  have hcn : ci.name = n := Env.find?_name hci
  have hmem := Env.find?_mem hci
  rw [henv] at hmem
  obtain ⟨d, hd, hcd⟩ | hnil :=
    (Driver.mem_streamEnv_consts (sideRecords justify ds).toList _).1 hmem
  case inr => exact absurd hnil List.not_mem_nil
  have hb := hbn d hd
  -- the name is reserved, and none of the quotient package's
  have hres : reservedBasisNames.contains n = true := by
    simp only [pinnedKinds, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;>
      simp only [BasisKind.decls, eqBasis, natBasis, emptyBasis, falseBasis, List.map_cons,
        List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hn <;>
      rcases hn with rfl | rfl | rfl | rfl <;> decide
  have hnq : ∀ (k : QuotKind) (cv : ConstantVal), (quotAt k cv).name ≠ n := by
    intro k cv hq
    have hqn : (quotAt k cv).name = (quotPin k).name := by
      unfold quotAt ConstantInfo.atLps
      cases quotPin k <;> rfl
    rw [hqn] at hq
    subst hq
    simp only [pinnedKinds, List.mem_cons, List.not_mem_nil, or_false] at hk
    cases k <;> rcases hk with rfl | rfl | rfl | rfl <;> revert hn <;> decide
  cases d with
  | defnDecl cv v hint =>
    obtain rfl := List.mem_singleton.mp hcd
    simp only [basisNamesOk, Bool.not_eq_true'] at hb
    rw [show cv.name = n from hcn, hres] at hb
    exact nomatch hb
  | thmDecl cv v =>
    obtain rfl := List.mem_singleton.mp hcd
    simp only [basisNamesOk, Bool.not_eq_true'] at hb
    rw [show cv.name = n from hcn, hres] at hb
    exact nomatch hb
  | opaqueDecl cv v =>
    obtain rfl := List.mem_singleton.mp hcd
    simp only [basisNamesOk, Bool.not_eq_true'] at hb
    rw [show cv.name = n from hcn, hres] at hb
    exact nomatch hb
  | quotDecl k cv =>
    obtain rfl := List.mem_singleton.mp hcd
    exact absurd hcn (hnq k cv)
  | axiomDecl cv =>
    simp only [declConstants] at hcd
    split at hcd
    · obtain rfl := List.mem_singleton.mp hcd
      exact absurd hcn (hnq .sound cv)
    split at hcd
    · exact absurd hcd List.not_mem_nil
    · next hsnd _ =>
      obtain rfl := List.mem_singleton.mp hcd
      simp only [basisNamesOk, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hb
      rcases hb with hb | hb
      · exact absurd hb hsnd
      · rw [show cv.name = n from hcn, hres] at hb
        exact nomatch hb
  | indDecl block nP =>
    refine ⟨block, nP, mem_sideRecords_ind hd, ?_⟩
    -- the name is one of the block's
    have hnb : n ∈ block.map (·.name) := by
      simp only [declConstants] at hcd
      split at hcd
      · next p hp =>
        obtain ⟨hm, hc, hr⟩ := readBlock_names hp
        have hcn' : ci.name ∈ (blockConstants p).map (·.name) := List.mem_map_of_mem hcd
        rw [blockConstants_names] at hcn'
        rw [← hcn]
        rcases List.mem_append.mp hcn' with h1 | h1
        · rcases List.mem_append.mp h1 with h2 | h2
          · obtain ⟨ms, hms, he⟩ := List.mem_map.mp h2
            obtain ⟨b, hb, hbn⟩ := hm ms hms
            exact List.mem_map.mpr ⟨b, hb, hbn.trans he⟩
          · obtain ⟨c, hc', he⟩ := List.mem_map.mp h2
            obtain ⟨b, hb, hbn⟩ := hc c hc'
            exact List.mem_map.mpr ⟨b, hb, hbn.trans he⟩
        · obtain ⟨rc, hrc, he⟩ := List.mem_map.mp h1
          obtain ⟨b, hb, hbn⟩ := hr rc hrc
          exact List.mem_map.mpr ⟨b, hb, hbn.trans he⟩
      · exact absurd hcd List.not_mem_nil
    simp only [basisNamesOk] at hb
    split at hb
    · next kind' hhit =>
      -- the block is the pinned block its names say, and the name says which
      have hkn : kind'.decls.map (·.name) = block.map (·.name) := by
        unfold basisNameHit at hhit
        have := List.find?_some hhit
        simpa using this
      have hk' : kind' = kind := by
        have hn' : n ∈ kind'.decls.map (·.name) := hkn ▸ hnb
        have hk'm : kind' ∈ pinnedKinds := List.mem_of_find?_eq_some hhit
        simp only [pinnedKinds, List.mem_cons, List.not_mem_nil, or_false] at hk hk'm
        rcases hk with rfl | rfl | rfl | rfl <;>
          simp only [BasisKind.decls, eqBasis, natBasis, emptyBasis, falseBasis, List.map_cons,
            List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hn <;>
          rcases hn with rfl | rfl | rfl | rfl <;>
          rcases hk'm with rfl | rfl | rfl | rfl <;> revert hn' <;> decide
      subst hk'
      simp only [pinListOk, Bool.and_eq_true] at hb
      exact hb.1
    · obtain ⟨b, hb', hbn⟩ := List.mem_map.mp hnb
      have := List.all_eq_true.mp hb b hb'
      rw [hbn, hres] at this
      exact nomatch this

/-- A record the pin comparison passes has the pin's name and type at its own level-parameter
names: distinct, as many as the pin's. -/
theorem pinCopyOk_cv {c pin : ConstantInfo} (h : pinCopyOk c pin = true)
    (hpin : pin.dropCaps = pin) :
    c.toConstantVal = (pin.atLps c.toConstantVal.levelParams).toConstantVal ∧
      Name.nodup c.toConstantVal.levelParams = true ∧
      c.toConstantVal.levelParams.length = pin.toConstantVal.levelParams.length := by
  have hd := pinCopyOk_dropCaps h hpin
  simp only [pinCopyOk, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨?_, h.1.1, h.1.2⟩
  have : c.dropCaps.toConstantVal = c.toConstantVal := by cases c <;> rfl
  exact this.symm.trans (by rw [hd])

/-- **An accepted stream that stores `False` declares the prelude's `False`.** -/
theorem checkDecls_declaresFalse {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {ds : Array Declaration} {justify : Option Env} {env : Env}
    (h : checkDeclsWith mode pins maxNatSize ds justify = .ok env)
    (hs : (env.find? falseName).isSome = true) : DeclaresFalse (· ∈ constantsOf ds.toList) := by
  obtain ⟨block, nP, hmem, hok⟩ := checkDecls_pinned h (kind := .falseK) (by decide)
    (n := falseName) (by decide) hs
  match block, hok with
  | [b1, b2], hok =>
    simp only [BasisKind.decls, falseBasis, listBeqBy, Bool.and_eq_true] at hok
    obtain ⟨hcv, -, hl⟩ := pinCopyOk_cv hok.2.1 rfl
    match hq : b2.toConstantVal.levelParams, hl with
    | [p], _ =>
      obtain ⟨c, hc, hcc⟩ : ∃ c ∈ ([b1, b2] : List ConstantInfo), c.toConstantVal = b2.toConstantVal :=
        ⟨b2, by simp, rfl⟩
      refine ⟨p, c, mem_constantsOf.2 ⟨_, hmem, hc⟩, ?_⟩
      rw [hcc, hcv, hq]
      rfl
  | [], hok | [_], hok | _ :: _ :: _ :: _, hok =>
    simp [BasisKind.decls, falseBasis, listBeqBy] at hok

/-- **An accepted stream that stores `Eq` declares the prelude's `Eq`.** -/
theorem checkDecls_declaresEq {mode : CheckMode} {pins : List NatOpPinSet} {maxNatSize : Nat}
    {ds : Array Declaration} {justify : Option Env} {env : Env}
    (h : checkDeclsWith mode pins maxNatSize ds justify = .ok env)
    (hs : (env.find? eqName).isSome = true) : DeclaresEq (· ∈ constantsOf ds.toList) := by
  obtain ⟨block, nP, hmem, hok⟩ := checkDecls_pinned h (kind := .eqK) (by decide)
    (n := eqName) (by decide) hs
  match block, hok with
  | [b1, b2, b3], hok =>
    simp only [BasisKind.decls, eqBasis, listBeqBy, Bool.and_eq_true] at hok
    obtain ⟨hcv1, -, hl1⟩ := pinCopyOk_cv hok.1 rfl
    obtain ⟨hcv2, -, hl2⟩ := pinCopyOk_cv hok.2.1 rfl
    obtain ⟨hcv3, hnd3, hl3⟩ := pinCopyOk_cv hok.2.2.1 rfl
    match hq1 : b1.toConstantVal.levelParams, hl1, hq2 : b2.toConstantVal.levelParams, hl2,
      hq3 : b3.toConstantVal.levelParams, hl3, hnd3 with
    | [p], _, [p'], _, [p₁, p₃], _, hnd =>
      obtain ⟨c1, hc1, hcc1⟩ : ∃ c ∈ ([b1, b2, b3] : List ConstantInfo),
          c.toConstantVal = b1.toConstantVal := ⟨b1, by simp, rfl⟩
      obtain ⟨c2, hc2, hcc2⟩ : ∃ c ∈ ([b1, b2, b3] : List ConstantInfo),
          c.toConstantVal = b2.toConstantVal := ⟨b2, by simp, rfl⟩
      obtain ⟨c3, hc3, hcc3⟩ : ∃ c ∈ ([b1, b2, b3] : List ConstantInfo),
          c.toConstantVal = b3.toConstantVal := ⟨b3, by simp, rfl⟩
      refine ⟨⟨p, c1, mem_constantsOf.2 ⟨_, hmem, hc1⟩, ?_⟩, ⟨p', c2, mem_constantsOf.2 ⟨_, hmem, hc2⟩, ?_⟩,
        ⟨p₁, p₃, ?_, c3, mem_constantsOf.2 ⟨_, hmem, hc3⟩, ?_⟩⟩
      · rw [hcc1, hcv1, hq1]; rfl
      · rw [hcc2, hcv2, hq2]; rfl
      · simpa [Name.nodup] using hnd
      · rw [hcc3, hcv3, hq3]; rfl
  | [], hok | [_], hok | [_, _], hok | _ :: _ :: _ :: _ :: _, hok =>
    simp [BasisKind.decls, eqBasis, listBeqBy] at hok

end ConLeche.Cached
