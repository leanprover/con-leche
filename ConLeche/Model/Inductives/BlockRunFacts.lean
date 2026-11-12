module

import ConLeche.Model.Inductives.DeclBlockStep
import ConLeche.Verify.Inductives.BlockShapeInv
public import ConLeche.Model.Inductives.FamilyRan
public import ConLeche.Semantics.Inductives.DeclBlock
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.GenRecC
import ConLeche.Verify.Cached.BlockPushes
import ConLeche.Semantics.Inductives.BlockConsFind

public section

/-!
# What a block's install adds to the environment

Read off the run alone: the constants it adds lie under its records' names, all of them fresh, and
its tables under its members' names. The fold's two environment facts (`NatFacts`, the tables on
old names) cross the install by these.
-/

namespace ConLeche.Model

open ConLeche ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory

universe w
variable {V : Type w} [SetTheory V]

omit [SetTheory V] in
/-- **The block's constants are under its records' names.** -/
theorem blockConstants_names_mem {nPd : Nat} {block : List ConstantInfo} {p₀ : BlockShape}
    (hdp : ConLeche.readBlock nPd block = .ok p₀) :
    ∀ n ∈ (ConLeche.blockConstants p₀).map (·.name), ∃ b ∈ block, b.name = n := by
  intro n hn
  rw [ConLeche.Cached.blockConstants_names] at hn
  obtain ⟨hM, hC, hR⟩ := ConLeche.readBlock_names hdp
  rcases List.mem_append.mp hn with hn | hn
  · rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hn
      exact hM ms hms
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
      exact hC c hc
  · obtain ⟨rc, hrc, rfl⟩ := List.mem_map.mp hn
    exact hR rc hrc

omit [SetTheory V] in
/-- What a list of constants consed onto an environment leaves unbound was unbound before. -/
theorem find?_none_of_append {env env' : Env} {new : List ConstantInfo}
    (h : env'.consts = new ++ env.consts) {n : Name} (hn : env'.find? n = none) :
    env.find? n = none := by
  show env.consts.find? (·.name == n) = none
  have : env'.consts.find? (·.name == n) = none := hn
  rw [h, List.find?_append] at this
  cases hx : new.find? (·.name == n) with
  | some x => rw [hx] at this; exact nomatch this
  | none => rw [hx] at this; exact this

omit [SetTheory V] in
/-- **A block's install pushes fresh names**: no name of `blockConstants` is bound before the
block (the formers' and the constructors' constant checks, the recursor stage's freshness). -/
theorem blockRun_fresh {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {p₀ : BlockShape}
    (hd : ∀ m ∈ p₀.members, m.declared = m.cvT)
    (hrun : ConLeche.Semantics.BlockRun F env block p₀ env₂) :
    ∀ n ∈ (ConLeche.blockConstants p₀).map (·.name), env.find? n = none := by
  obtain ⟨ms, hms, -, -, hR⟩ := hrun
  obtain ⟨-, -, -, isRec, env₁, p₁, sortsss, ctx, holes, rd, Ms, kinds,
    nfs, nodes, st, isorts, outR, -, hInd, hCtors, -, -, -, -, -, -, hRec, -, -, -, -, -⟩ := hR
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, -, hq, hcons, -, -, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  obtain ⟨-, -, hname, -, hctors⟩ := ConLeche.reduceMembers_inv hd hms
  have hext₁ : ∀ n, env₁.find? n = none → env.find? n = none := fun n hn => by
    rw [hcons, ConLeche.consBlockInds_consts'] at hn
    exact find?_none_of_append rfl hn
  have hext₂ : ∀ n, (ConLeche.consBlockCtors p₁.nP p₁.ctorGroups env₁).find? n = none →
      env₁.find? n = none := fun n hn =>
    find?_none_of_append (consBlockCtors_consts p₁.nP p₁.ctorGroups env₁) hn
  have hRec' : ConLeche.genRecCheck (ConLeche.fueledOps .verified F)
      (mkFEnv (ConLeche.consBlockCtors p₁.nP p₁.ctorGroups env₁)) p₁
      (ConLeche.blockNestedBit p₁ kinds) ctx.params st.ctorNfs.toList
      rd Ms block = .ok outR := hRec
  intro n hn
  rw [ConLeche.Cached.blockConstants_names] at hn
  rcases List.mem_append.mp hn with hn | hn
  · rcases List.mem_append.mp hn with hn | hn
    · -- a former: its constant check, at the block's environment
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      have hmn : m.cvT.name ∈ ms.map (·.cvT.name) := by
        rw [hname]; exact List.mem_map_of_mem hm
      obtain ⟨m', hm', he⟩ := List.mem_map.mp hmn
      rw [hd m hm, ← he]
      exact ConLeche.Semantics.checkBlockInds_fresh hInd m'.cvT (List.mem_map_of_mem hm')
    · -- a constructor: its constant check, at the formers' environment
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
      obtain ⟨L, hL, hcL⟩ := List.mem_flatten.mp hc
      have hL₁ : L ∈ p₁.members.map (·.ctors) := by
        rw [hq]
        show L ∈ ms.map (·.ctors)
        rw [hctors]
        exact hL
      exact hext₁ _ (ConLeche.checkBlockCtors_fresh hCtors L hL₁ c hcL)
  · -- a recursor: the recursor stage's, at the constructors' environment
    obtain ⟨rc, hrc, rfl⟩ := List.mem_map.mp hn
    have hrc₁ : rc ∈ p₁.recs := by rw [hq]; exact hrc
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hrc₁
    obtain ⟨hlen, hcv⟩ := ConLeche.Cached.genRecCheck_outCv hRec'
    have hil : i < outR.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1; omega
    have ho : outR[i]? = some outR[i] := List.getElem?_eq_getElem hil
    have hn' : outR[i].1.name = rc.cvR.name := by rw [hcv i rc _ hi ho]
    rw [← hn']
    exact hext₁ _ (hext₂ _ (ConLeche.genRecCheck_out_fresh hRec' _ (List.getElem_mem hil)))

omit [SetTheory V] in
/-- **`Nat`'s block is stored at once across an unreserved block's install.** -/
theorem natFacts_block {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {nPd : Nat}
    {p₀ : BlockShape} (hN : NatFacts env) (hdp : ConLeche.readBlock nPd block = .ok p₀)
    (hres : ∀ c ∈ block, ConLeche.reservedBasisNames.contains c.name = false)
    (hrun : ConLeche.Semantics.BlockRun F env block p₀ env₂) : NatFacts env₂ := by
  have henv := ConLeche.Semantics.blockRun_env (ConLeche.readBlock_declared hdp) hrun
  refine hN.append (new := (ConLeche.blockConstants p₀).reverse) (by rw [henv]; rfl) fun c hc => ?_
  obtain ⟨b, hb, hn⟩ :=
    blockConstants_names_mem hdp c.name (List.mem_map_of_mem (List.mem_reverse.mp hc))
  exact nat_names_of_unreserved (hn ▸ hres b hb)

omit [SetTheory V] in
/-- The install's tables on the old names. -/
theorem blockRun_findTable {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {nPd : Nat}
    {p₀ : BlockShape} (hdp : ConLeche.readBlock nPd block = .ok p₀)
    (hrun : ConLeche.Semantics.BlockRun F env block p₀ env₂) (T : Name)
    (hT : (env.find? T).isSome = true) : env₂.findTable? T = env.findTable? T := by
  have hd := ConLeche.readBlock_declared hdp
  have henv := ConLeche.Semantics.blockRun_env hd hrun
  have hfr := blockRun_fresh hd hrun
  -- a new table is at a member's name, unbound before the block
  have hne : ∀ t ∈ ((ConLeche.blockTables p₀ p₀.members).getD []).reverse,
      (t.structName == T) = false := by
    intro t ht
    obtain ⟨m, hm, hn⟩ : ∃ m ∈ p₀.members, t.structName = m.declared.name := by
      cases hQ : ConLeche.blockTables p₀ p₀.members with
      | none => simp only [hQ, Option.getD_none, List.reverse_nil, List.not_mem_nil] at ht
      | some Q =>
        simp only [hQ, Option.getD_some, List.mem_reverse] at ht
        exact ConLeche.blockTables_names _ _ Q hQ t ht
    have hf := hfr m.declared.name (by
      rw [ConLeche.Cached.blockConstants_names]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hm)))
    rw [beq_eq_false_iff_ne]
    intro he
    have hfT : env.find? T = none := by rw [← he, hn]; exact hf
    rw [hfT] at hT
    exact nomatch hT
  have hs₂ : (env₂.find? T).isSome = true := by
    show (env₂.consts.find? (·.name == T)).isSome = true
    rw [henv]
    show (((ConLeche.blockConstants p₀).reverse ++ env.consts).find? (·.name == T)).isSome = true
    rw [List.find?_append, Option.isSome_or]
    exact Bool.or_eq_true_iff.mpr (Or.inr hT)
  unfold Env.findTable?
  rw [hs₂, hT, henv]
  show (((ConLeche.blockTables p₀ p₀.members).getD []).reverse ++ env.tables).find? _ = _
  rw [List.find?_append, List.find?_eq_none.mpr (fun t ht => by simp [hne t ht])]
  rfl

/-- **The uniform block step, at a recognised block whose records take no reserved name.** -/
theorem declBlock {F : Nat} {env env₂ : Env} {block : List ConstantInfo} {nPd : Nat} {p₀ : BlockShape}
    (mp : EnvModelM V env)
    (hdp : ConLeche.readBlock nPd block = .ok p₀)
    -- the reserved names' check (`basisNamesOk`), at a block no pinned one's
    (hres : ∀ c ∈ block, ConLeche.reservedBasisNames.contains c.name = false)
    (hrun : ConLeche.Semantics.BlockRun F env block p₀ env₂) (hcov : LfpCover mp [])
    (hRan : FamilyRan mp) (hNat : NatFacts env) :
    (∃ mp' : EnvModelM V env₂, LfpCover mp' [] ∧ FamilyRan mp') ∧ NatFacts env₂ := by
  have hrun₀ := hrun
  obtain ⟨ms, hms, hAt, -, hR⟩ := hrun
  obtain ⟨-, -, -, hmembersOk, hClps₀, -, -, -⟩ :=
    ConLeche.readBlock_inv hdp
  have hd := ConLeche.readBlock_declared hdp
  obtain ⟨hM, hC, hRc⟩ := ConLeche.readBlock_names hdp
  obtain ⟨-, hdc, hnm, -, hct⟩ := ConLeche.reduceMembers_inv hd hms
  have hlps : ∀ m ∈ ms, m.cvT.levelParams = p₀.lps := by
    intro m hm
    have hm' : m.declared ∈ p₀.members.map (·.declared) := by
      rw [← hdc]; exact List.mem_map_of_mem hm
    obtain ⟨m₀, hm₀, he⟩ := List.mem_map.mp hm'
    rw [(hAt m hm).lps, ← he, hd m₀ hm₀]
    exact hmembersOk m₀ hm₀
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
  -- the reserved names' check, at the members, the constructors and the recursors
  have hresC : ∀ c ∈ p₀.allCtors, ConLeche.reservedBasisNames.contains c.1.name = false :=
    fun c hc => by obtain ⟨b, hb, hn⟩ := hC c hc; exact hn ▸ hres b hb
  have hresM : ∀ m ∈ ({ p₀ with members := ms } : BlockShape).members,
      ConLeche.reservedBasisNames.contains m.cvT.name = false := by
    intro m hm
    have hmn : m.cvT.name ∈ p₀.members.map (·.cvT.name) := by
      rw [← hnm]; exact List.mem_map_of_mem hm
    obtain ⟨m₀, hm₀, he⟩ := List.mem_map.mp hmn
    obtain ⟨b, hb, hn⟩ := hM m₀ hm₀
    rw [← he, ← hd m₀ hm₀, ← hn]
    exact hres b hb
  have hresR : ∀ rc ∈ ({ p₀ with members := ms } : BlockShape).recs,
      ConLeche.reservedBasisNames.contains rc.cvR.name = false :=
    fun rc hrc => by obtain ⟨b, hb, hn⟩ := hRc rc hrc; exact hn ▸ hres b hb
  refine ⟨declBlockAt (p₀ := { p₀ with members := ms }) mp
    (fun m hm => (hlps m hm).trans hlpsEq.symm) hAt
    (fun c hc => by rw [hlpsEq]; exact ⟨hClps₀ c (hctors c hc), hresC c (hctors c hc)⟩)
    hresM hresR hR hcov hRan hNat (blockRun_findTable hdp hrun₀),
    natFacts_block hNat hdp hres hrun₀⟩

end ConLeche.Model
