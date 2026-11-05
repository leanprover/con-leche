module

import ConLeche.Model.Inductives.DeclBlockStep
import ConLeche.Verify.Inductives.BlockShapeInv
public import ConLeche.Model.Inductives.FamilyRan
public import ConLeche.Semantics.Inductives.DeclBlock
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Semantics.Inductives.DeclBlockEta
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.GenRecC

public section

/-!
# What a block's install adds to the environment

Read off the run alone: the constants it adds lie under unreserved names, its tables under its
members' fresh names. The fold's two environment facts (`NatFacts`, the tables on old names) cross
the install by these.
-/

namespace ConLeche.Model

open ConLeche ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory

universe w
variable {V : Type w} [SetTheory V]

omit [SetTheory V] in
theorem consBlockInds_indexed {p₁ : BlockShape} {isRec : Bool} :
    ∀ (cvs : List ConstantVal) (i : Nat) (env : Env), ∃ new : List ConstantInfo,
      (ConLeche.consBlockInds p₁ isRec cvs i env).consts = new ++ env.consts ∧
      ∀ c ∈ new, ∃ j cv, cvs[j]? = some cv ∧ c = .indInfo cv (ConLeche.blockCapsAt p₁ (i + j) isRec)
  | [], _, _ => ⟨[], rfl, fun _ h => nomatch h⟩
  | cv :: rest, i, env => by
    obtain ⟨new, hnew, hall⟩ := consBlockInds_indexed (p₁ := p₁) (isRec := isRec) rest (i + 1)
      ⟨.indInfo cv (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩
    refine ⟨new ++ [.indInfo cv (ConLeche.blockCapsAt p₁ i isRec)], ?_, fun c hc => ?_⟩
    · show (ConLeche.consBlockInds p₁ isRec rest (i + 1) _).consts = _
      rw [hnew]; simp
    · rcases List.mem_append.mp hc with h | h
      · obtain ⟨j, cv', hj, rfl⟩ := hall c h
        exact ⟨j + 1, cv', by simpa using hj, by
          rw [show i + (j + 1) = i + 1 + j by omega]⟩
      · rw [List.mem_singleton.mp h]
        exact ⟨0, cv, rfl, rfl⟩

omit [SetTheory V] in
/-- A stored recursor is named as the generated one. -/
theorem streamRecs_mem_name :
    ∀ (recs : List RecShape) (out : List (ConstantVal × ConLeche.TargetMajor × List Expr)),
      ∀ o ∈ ConLeche.streamRecs recs out, ∃ g ∈ out, o.1.name = g.1.name
  | [], _, _, h => by simp [ConLeche.streamRecs] at h
  | _ :: _, [], _, h => by simp [ConLeche.streamRecs] at h
  | rc :: recs, g :: out, o, h => by
    simp only [ConLeche.streamRecs, List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨g, List.mem_cons_self, rfl⟩
    · obtain ⟨g', hg', hn⟩ := streamRecs_mem_name recs out o h
      exact ⟨g', List.mem_cons_of_mem _ hg', hn⟩

omit [SetTheory V] in
/-- **What the install adds**: constants under unreserved names. -/
theorem declBlockRun_consts {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    {p₀ : BlockShape} (hrun : ConLeche.Semantics.DeclBlockRun F env block p₀ env₂)
    (hdn : ∀ ms ∈ p₀.members, ms.declared.name = ms.cvT.name) :
    ∃ new : List ConstantInfo, env₂.consts = new ++ env.consts ∧
      ((∀ c ∈ p₀.allCtors, ConLeche.reservedBasisNames.contains c.1.name = false) →
        ∀ c ∈ new, ConLeche.reservedBasisNames.contains c.name = false) := by
  obtain ⟨-, -, -, isRec, env₁, p₁, sortsss, ctx, holes, rd, Ms, kinds,
    nfs, nodes, st, isorts, outR, hInd, hCtors, -, -, -, -, -, -, hRec, -, -, -, hfin⟩ := hrun
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, hmem0, hq, hcons, htele0, hteles, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  obtain ⟨newI, hnewI, hnewIall⟩ := consBlockInds_indexed (p₁ := p₁) (isRec := isRec)
    (p₀.members.map (·.declared)) 0 env
  obtain ⟨newR, hnewR, hnewRall⟩ := consBlockRecsT_consts
    (q := p₁) 0 (ConLeche.streamRecs p₁.recs outR)
    (ConLeche.consBlockCtors p₁.nP p₁.memberCtors env₁)
  have hctor := consBlockCtors_consts p₁.nP p₁.memberCtors env₁
  refine ⟨newR ++ (p₁.memberCtors.flatten.map fun c => ConstantInfo.ctorInfo c.1 p₁.nP c.2).reverse ++ newI,
    ?_, fun hCres c hc => ?_⟩
  · rw [hfin]
    show (ConLeche.consBlockRecsT _ 0 _ _).consts = _
    rw [hnewR, hctor, hcons, hnewI]
    simp
  · simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · obtain ⟨o, ho, mI, rP, isK, rules, rfl⟩ := hnewRall c hc
      obtain ⟨g, hg, hn⟩ := streamRecs_mem_name _ _ o ho
      have hRec' : ConLeche.genRecCheck (ConLeche.ShadowOps.fueled .verified F)
          (mkFEnv (ConLeche.consBlockCtors p₁.nP p₁.memberCtors env₁)) p₁
          (ConLeche.blockNestedBit p₁ kinds) ctx.params st.ctorNfs.toList
          rd Ms block = .ok outR := hRec
      have hr := ConLeche.Cached.genRecCheck_out_unreserved hRec' g hg
      have hn' : (ConstantInfo.recInfo o.1 mI rP isK rules).name = g.1.name := hn
      rw [hn']
      simp only [ConLeche.reservedRecName, Bool.or_eq_false_iff] at hr
      exact hr.1.1.1.1.1.1
    · obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
      obtain ⟨ctorList, hctorList, hcAm⟩ := List.mem_flatten.mp hctor
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hctorList
      have hmm : m ∈ p₀.members := by
        have : p₁.members = p₀.members := by rw [hq]; rfl
        rw [← this]; exact hm
      exact hCres ctor (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨m, hmm, rfl⟩, hcAm⟩)
    · obtain ⟨j, cv', hj, rfl⟩ := hnewIall c hc
      rw [List.getElem?_map] at hj
      cases hmsj : p₀.members[j]? with
      | none => rw [hmsj] at hj; exact nomatch hj
      | some ms =>
        rw [hmsj] at hj
        obtain rfl : ms.declared = cv' := by simpa using hj
        have hms := List.mem_of_getElem? hmsj
        have hnm := hdn ms hms
        have hrun₁ : ∃ q, ConLeche.checkBlockTele (fueledOps .verified F) env p₀.nP ms = .ok q := by
          rw [hmem0] at hms
          rcases List.mem_cons.mp hms with rfl | hms'
          · exact ⟨_, htele0⟩
          · obtain ⟨i, hi⟩ := List.getElem?_of_mem hms'
            obtain ⟨q, -, hq'⟩ := (ConLeche.checkBlockTeles_inv hteles).2 i ms hi
            exact ⟨q, hq'⟩
        obtain ⟨q, hq'⟩ := hrun₁
        unfold ConLeche.checkBlockTele at hq'
        obtain ⟨u, hc', -⟩ := exceptBind_ok hq'
        cases u
        show ConLeche.reservedBasisNames.contains ms.declared.name = false
        rw [hnm]
        exact (ConLeche.checkConstantVal_inv hc').2.1

omit [SetTheory V] in
/-- **The ordinary install's tables and its fresh members.** -/
theorem declBlockRun_tables {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    {p₀ : BlockShape} (hrun : ConLeche.Semantics.DeclBlockRun F env block p₀ env₂)
    (hdn : ∀ ms ∈ p₀.members, ms.declared.name = ms.cvT.name) :
    (∀ ms ∈ p₀.members, env.find? ms.cvT.name = none) ∧
    ∃ newQ : List ProjTable, env₂.tables = newQ ++ env.tables ∧
      ∀ t ∈ newQ, ∃ ms ∈ p₀.members, t.structName = ms.cvT.name := by
  obtain ⟨-, -, -, isRec, env₁, p₁, sortsss, ctx, holes, rd, Ms, kinds,
    nfs, nodes, st, isorts, outR, hInd, -, -, -, -, -, -, -, -, -, -, -, hfin⟩ := hrun
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, hmem0, hq, hcons, htele0, hteles, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  refine ⟨?_, ?_⟩
  · intro ms hms
    have hrun₁ : ∃ q, ConLeche.checkBlockTele (fueledOps .verified F) env p₀.nP ms = .ok q := by
      rw [hmem0] at hms
      rcases List.mem_cons.mp hms with rfl | hms'
      · exact ⟨_, htele0⟩
      · obtain ⟨i, hi⟩ := List.getElem?_of_mem hms'
        obtain ⟨q, -, hq'⟩ := (ConLeche.checkBlockTeles_inv hteles).2 i ms hi
        exact ⟨q, hq'⟩
    obtain ⟨q, hq'⟩ := hrun₁
    unfold ConLeche.checkBlockTele at hq'
    obtain ⟨u, hc, -⟩ := exceptBind_ok hq'
    cases u
    exact (ConLeche.checkConstantVal_inv hc).1
  · have hmm : p₁.members = p₀.members := by rw [hq]; rfl
    refine ⟨(ConLeche.blockTables p₁ p₁.members).reverse,
      ?_, fun t ht => ?_⟩
    · rw [hfin]
      show _ ++ (ConLeche.consBlockRecsT _ 0 _ _).tables = _
      rw [consBlockRecsT_tables 0, consBlockCtors_tables, hcons, consBlockInds_tables]
    · obtain ⟨m, hm, hn⟩ := ConLeche.Cached.blockTables_names _ _ t (List.mem_reverse.mp ht)
      have hm' : m ∈ p₀.members := hmm ▸ hm
      exact ⟨m, hm', hn.trans (hdn m hm')⟩

omit [SetTheory V] in
/-- **`Nat`'s block is stored at once across the block's install.** -/
theorem natFacts_block {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {p₀ : BlockShape}
    (hN : NatFacts env)
    (hClps₀ : ∀ c ∈ p₀.allCtors, ConLeche.reservedBasisNames.contains c.1.name = false)
    (hrun : ConLeche.Semantics.DeclBlockRun F env block p₀ env₂)
    (hdn : ∀ ms ∈ p₀.members, ms.declared.name = ms.cvT.name) : NatFacts env₂ := by
  obtain ⟨new, hnew, hres⟩ := declBlockRun_consts hrun hdn
  exact hN.append hnew fun c hc => nat_names_of_unreserved (hres hClps₀ c hc)

omit [SetTheory V] in
/-- The ordinary install's tables on the old names. -/
theorem declBlockRun_findTable {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    {p₀ : BlockShape} (hrun : ConLeche.Semantics.DeclBlockRun F env block p₀ env₂)
    (hdn : ∀ ms ∈ p₀.members, ms.declared.name = ms.cvT.name) (T : Name)
    (hT : (env.find? T).isSome = true) : env₂.findTable? T = env.findTable? T := by
  obtain ⟨hfresh, newQ, hQ, hQall⟩ := declBlockRun_tables hrun hdn
  obtain ⟨new, hnew, -⟩ := declBlockRun_consts hrun hdn
  have hne : ∀ t ∈ newQ, (t.structName == T) = false := by
    intro t ht
    obtain ⟨m, hm, hn⟩ := hQall t ht
    have := hfresh m hm
    rw [beq_eq_false_iff_ne]
    intro he
    rw [← hn, he] at this
    rw [this] at hT
    exact nomatch hT
  have hs₂ : (env₂.find? T).isSome = true := by
    show (env₂.consts.find? (·.name == T)).isSome = true
    rw [hnew, List.find?_append, Option.isSome_or]
    exact Bool.or_eq_true_iff.mpr (Or.inr hT)
  unfold Env.findTable?
  rw [hs₂, hT]
  simp only [hQ, List.find?_append]
  rw [List.find?_eq_none.mpr (fun t ht => by simp [hne t ht])]
  rfl

/-- **The uniform block step, at a recognised block.** -/
theorem declBlock {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {nPd : Nat} {p₀ : BlockShape}
    (mp : EnvModelM V env) (hE : ConLeche.EtaFamiliesClosed env)
    (hdp : ConLeche.blockShape? nPd block = some p₀)
    (hrun : ConLeche.Semantics.BlockRun F env block p₀ env₂) (hcov : LfpCover mp [])
    (hRan : FamilyRan mp) (hNat : NatFacts env) :
    (∃ mp' : EnvModelM V env₂, LfpCover mp' [] ∧ FamilyRan mp') ∧ NatFacts env₂ := by
  obtain ⟨ms, hms, hAt, -, hR⟩ := hrun
  obtain ⟨-, -, -, hmembersOk, -, hClps₀, -, -, -⟩ :=
    ConLeche.blockShape?_inv hdp
  have hd := ConLeche.blockShape?_declared hdp
  obtain ⟨-, hdc, -, -, hct⟩ := ConLeche.reduceMembers_inv hd hms
  have hlps : ∀ m ∈ ms, m.cvT.levelParams = p₀.lps := by
    intro m hm
    have hm' : m.declared ∈ p₀.members.map (·.declared) := by
      rw [← hdc]; exact List.mem_map_of_mem hm
    obtain ⟨m₀, hm₀, he⟩ := List.mem_map.mp hm'
    rw [(hAt m hm).lps, ← he, hd m₀ hm₀]
    exact (hmembersOk m₀ hm₀).1
  have hlpsEq : ({ p₀ with members := ms } : BlockShape).lps = p₀.lps := by
    show (ms.head?.map (·.cvT.levelParams)).getD [] = _
    cases hh : ms with
    | nil =>
      have hl : p₀.members = [] := by
        have := congrArg List.length hdc
        rw [hh] at this
        simpa using this.symm
      show _ = (p₀.members.head?.map (·.cvT.levelParams)).getD []
      rw [hl]
    | cons m rest =>
      show m.cvT.levelParams = _
      exact hlps m (by rw [hh]; exact List.mem_cons_self)
  have hctors : ∀ c, c ∈ ({ p₀ with members := ms } : BlockShape).allCtors → c ∈ p₀.allCtors := by
    intro c hc
    have he : ({ p₀ with members := ms } : BlockShape).allCtors = p₀.allCtors := by
      show (ms.map (·.ctors)).flatten = (p₀.members.map (·.ctors)).flatten
      rw [hct]
    rwa [he] at hc
  have hdn : ∀ m ∈ ({ p₀ with members := ms } : BlockShape).members,
      m.declared.name = m.cvT.name := fun m hm => (hAt m hm).name.symm
  refine ⟨declBlockAt (p₀ := { p₀ with members := ms }) mp hE
    (fun m hm => (hlps m hm).trans hlpsEq.symm) hAt
    (fun c hc => by rw [hlpsEq]; exact hClps₀ c (hctors c hc)) hR hcov hRan hNat
    (declBlockRun_findTable hR hdn),
    natFacts_block (p₀ := { p₀ with members := ms }) hNat
      (fun c hc => (hClps₀ c (hctors c hc)).2) hR hdn⟩

end ConLeche.Model
