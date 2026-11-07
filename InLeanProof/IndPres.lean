module

public import InLeanProof.EnvPresI

/-!
# An inductive block and the relation: the assembly and the capabilities (task #451, lane P3b)

**Not proved here: `IndGroupPres`.**  Two findings about it:

* *False as stated.*  Its premises constrain `consts` only through
  `storedBlock consts` (the formers, constructors and recursors), while the
  conclusion adds every constant of `consts` to InLean's environment.  A
  `consts` holding one more fresh, in-range constant of another kind (an
  axiom `foo`) passes every premise, and InLean then finds `foo` where
  con-leche's install has nothing, so `EnvPresI`'s `entry` fails.  The
  generator produces only block constants; `IndGroupPresB` adds that as a
  premise (`∀ ci ∈ consts, ci ∈ storedBlock consts`), which `checkInductiveC`
  checks (`isBlockConst`; `storedBlock_of_checkInductiveC`, `StepPres.lean`).
* *The projection bodies' range.*  `TableRelI` relates `projBodyAt`'s body
  through its reading, and InLean's instantiation is read only on terms in
  range (`toExpr_instantiate`).  `projBodyAt` instantiates by `bvar`s,
  which `EO.liftLooseBVars` lifts unchecked: a constructor type in range can
  yield a body that is not (`EnvBodiesPres.lean`), so the table clause needs
  the bodies in range, which `checkInductiveC` tests
  (`FEnv.projBodiesInRange`).

**Proved here.**
* `presI_group`: the step for a group of fresh, distinct constants added in
  any order (`foldl addConst`), from the group's own names: con-leche's
  installed constants and tables at the group's names, Lean's entries
  related to the installed ones, the tables related.  It discharges
  `presI_push`'s bookkeeping (the lookups after the fold, `sorryAx`'s
  visibility); `indGroupPresB_of` reduces `IndGroupPresB` to
  `BlockPresObl`, what remains to prove of the block's install.
* `toCaps_capsOf`: a former's capabilities as InLean reads them
  (`capsOf`) are con-leche's `blockCapsAt`, given what `genEntriesAgree`
  checks of the generated entry against InLean's shape and that shape's
  agreement with con-leche's (the member's constructors, index count,
  parameter count, block members and `isRec`).
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## Adding a list of fresh constants -/

/-- **The lookups after adding fresh, distinct constants**: each is found,
every other name reads as before. -/
theorem find_foldl_addConst (hlaws : EnvLaws) :
    ∀ (cs : List Lean.ConstantInfo) (E : Kernel.Environment),
      (∀ ci ∈ cs, E.find? ci.name = none) → (cs.map (·.name)).Nodup →
      (∀ ci ∈ cs, (cs.foldl InLean.addConst E).find? ci.name = some ci) ∧
      (∀ n, n ∉ cs.map (·.name) → (cs.foldl InLean.addConst E).find? n = E.find? n)
  | [], _, _, _ => ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl⟩
  | c :: cs, E, hf, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hc := hf c List.mem_cons_self
    have hf' : ∀ ci ∈ cs, (InLean.addConst E c).find? ci.name = none := by
      intro ci hci
      rw [find_addConst hlaws hc]
      have hne : ci.name ≠ c.name := fun he => hnd.1 (he ▸ List.mem_map_of_mem hci)
      simp only [hne, ↓reduceIte]
      exact hf ci (List.mem_cons_of_mem _ hci)
    obtain ⟨ih1, ih2⟩ := find_foldl_addConst hlaws cs (InLean.addConst E c) hf' hnd.2
    refine ⟨?_, ?_⟩
    · intro ci hci
      rcases List.mem_cons.1 hci with rfl | hci
      · show (cs.foldl InLean.addConst (InLean.addConst E ci)).find? ci.name = some ci
        rw [ih2 ci.name hnd.1, find_addConst hlaws hc]; simp
      · exact ih1 ci hci
    · intro n hn
      simp only [List.map_cons, List.mem_cons, not_or] at hn
      show (cs.foldl InLean.addConst (InLean.addConst E c)).find? n = _
      rw [ih2 n hn.2, find_addConst hlaws hc]
      simp [hn.1]

variable {fe : InLean.FEnv} {L : ConLeche.Env}

/-- **A group of fresh, distinct constants keeps the relation**, from the
group's own names (`presI_push`, with the lookups after the fold discharged),
every constant seen (`FEnv.sees`: safe, not at `sorryAx`'s name at
con-leche's policy). -/
theorem presI_group (hlaws : EnvLaws) (hP : EnvPresI fe L) {cs : List Lean.ConstantInfo}
    (hfresh : ∀ ci ∈ cs, fe.env.find? ci.name = none) (hnd : (cs.map (·.name)).Nodup)
    (hsees : ∀ ci ∈ cs, fe.sees ci.name ci = true)
    {news : List ConLeche.ConstantInfo} {tabs : List ConLeche.ProjTable}
    (hnewC : ∀ c ∈ news, ∃ ci ∈ cs, c.name = toName ci.name)
    (hnewT : ∀ t ∈ tabs, ∃ ci ∈ cs, t.structName = toName ci.name)
    (hentry : ∀ ci ∈ cs, ∃ cci, (L.pushDelta news tabs).find? (toName ci.name) = some cci ∧
      EntryRelI { fe with env := cs.foldl InLean.addConst fe.env } ci cci)
    (htab : ∀ ci ∈ cs, TableRelI { fe with env := cs.foldl InLean.addConst fe.env } ci.name
      ((L.pushDelta news tabs).findTable? (toName ci.name)))
    (htabFound : ∀ t ∈ tabs, ((L.pushDelta news tabs).find? t.structName).isSome) :
    EnvPresI { fe with env := cs.foldl InLean.addConst fe.env } (L.pushDelta news tabs) := by
  obtain ⟨hin, hout⟩ := find_foldl_addConst hlaws cs fe.env hfresh hnd
  have hfind : ∀ ci ∈ cs, ({ fe with env := cs.foldl InLean.addConst fe.env } : InLean.FEnv).find? ci.name =
      some ci := by
    intro ci hci
    rw [FEnv.find?_eq_filter]
    show ((cs.foldl InLean.addConst fe.env).find? ci.name).filter (fe.sees ci.name) = some ci
    rw [hin ci hci, Option.filter_some]; simp only [hsees ci hci, ↓reduceIte]
  apply presI_push (fe' := { fe with env := cs.foldl InLean.addConst fe.env })
    (names := cs.map (·.name)) hP rfl rfl rfl
  · intro n hn
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
    exact hfresh ci hci
  · exact hout
  · intro c hc
    obtain ⟨ci, hci, he⟩ := hnewC c hc
    exact ⟨ci.name, List.mem_map_of_mem hci, he⟩
  · intro t ht
    obtain ⟨ci, hci, he⟩ := hnewT t ht
    exact ⟨ci.name, List.mem_map_of_mem hci, he⟩
  · intro n hn ci' hf
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
    rw [hfind ci hci, Option.some.injEq] at hf
    subst hf
    exact hentry _ hci
  · intro n hn hf
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
    rw [hfind ci hci] at hf; cases hf
  · intro T hT
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hT
    exact htab ci hci
  · exact htabFound

/-! ## The inductive group, restated -/

/-- **An inductive block keeps the relation**: `IndGroupPres` with the
premise that the generator's constants are the stored block's (without it
the statement is false, see the module docstring). -/
@[expose] def IndGroupPresB : Prop :=
  EnvLaws → ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (consts : Array Lean.ConstantInfo) (nP : Nat)
    (s s' : InLean.CState) (d : ConLeche.Declaration),
    EnvPresI fe L →
    (∀ ci ∈ consts.toList, ci ∈ InLean.storedBlock consts) →
    (∀ ci ∈ consts.toList, fe.env.find? ci.name = none) → (consts.toList.map (·.name)).Nodup →
    (∀ ci ∈ consts.toList, fe.sees ci.name ci = true) →
    consts.all InLean.constInRange = true →
    (InLean.checkIndDeclC .verified fe (InLean.storedBlock consts) nP).run s = .ok ((), s') →
    toDecl (InLean.storedBlock consts) = some d →
    EnvPresI { fe with env := consts.foldl InLean.addConst fe.env }
      (L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d))

/-- **What remains of an inductive block**: con-leche's install of the
record, against the generated constants, at their names only — the
installed constants and tables named after the block's constants, each
generated constant related to the installed one at its name, each name's
table related, each installed table at an installed constant. -/
@[expose] def BlockPresObl : Prop :=
  EnvLaws → ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (consts : Array Lean.ConstantInfo) (nP : Nat)
    (s s' : InLean.CState) (d : ConLeche.Declaration),
    EnvPresI fe L →
    (∀ ci ∈ consts.toList, ci ∈ InLean.storedBlock consts) →
    (∀ ci ∈ consts.toList, fe.env.find? ci.name = none) → (consts.toList.map (·.name)).Nodup →
    consts.all InLean.constInRange = true →
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

/-- **The block's step from what remains of it** (`presI_group`). -/
theorem indGroupPresB_of (h : BlockPresObl) : IndGroupPresB := by
  intro hlaws fe L consts nP s s' d hP hblk hfresh hnd hsees hrange hrun hd
  obtain ⟨h1, h2, h3, h4, h5⟩ := h hlaws fe L consts nP s s' d hP hblk hfresh hnd hrange hrun hd
  rw [← Array.foldl_toList]
  exact presI_group hlaws hP hfresh hnd hsees h1 h2 h3 h4 h5

/-! ## A former's capabilities -/

/-- **`capsOf` is `blockCapsAt`**, given the member's data: the generated
entry's constructors, index and parameter counts, members and `isRec`
(what `genEntriesAgree` checks against InLean's shape), read as
con-leche's shape's member `mi`, and the one constructor's field count
where there is one (`FEnv.fieldsOf`: the stored constructor's, or the
shape's for a member of the block being checked). -/
theorem toCaps_capsOf {fe : InLean.FEnv} {v : InductiveVal} {p : ConLeche.BlockShape}
    {mi : Nat} {isRec : Bool}
    (hcs : v.ctors.map toName = (p.members.getD mi default).ctors.map (·.1.name))
    (hidx : v.numIndices = (p.members.getD mi default).nIdx) (hnP : v.numParams = p.nP)
    (hall : v.all.map toName = p.memberNames) (hrec : v.isRec = isRec)
    (hnF : ∀ c cc, v.ctors = [c] → (p.members.getD mi default).ctors = [cc] →
      fe.fieldsOf v c = cc.2) :
    toCaps (capsOf fe v) = ConLeche.blockCapsAt p mi isRec := by
  unfold ConLeche.blockCapsAt capsOf
  generalize hms : p.members.getD mi default = ms at hcs hidx hnF
  cases hv : v.ctors with
  | nil =>
    rw [hv] at hcs
    cases hc : ms.ctors with
    | nil => simp [toCaps, hall, hidx, hnP]; rfl
    | cons _ _ => rw [hc] at hcs; cases hcs
  | cons c rest =>
    rw [hv] at hcs
    cases hc : ms.ctors with
    | nil => rw [hc] at hcs; cases hcs
    | cons cc rest' =>
      rw [hc] at hcs
      simp only [List.map_cons, List.cons.injEq] at hcs
      cases rest with
      | nil =>
        cases rest' with
        | nil =>
          simp [toCaps, hnF c cc hv hc, hall, hidx, hnP, hrec, hcs.1]
        | cons _ _ => cases hcs.2
      | cons c2 rest2 =>
        cases rest' with
        | nil => cases hcs.2
        | cons cc2 rest2' =>
          simp only [toCaps, List.map_cons, hall, hidx, hnP, hcs.1]
          rw [show rest2.map toName = rest2'.map (·.1.name) from (List.cons.inj hcs.2).2,
            show toName c2 = cc2.1.name from (List.cons.inj hcs.2).1]
          rfl

end InLeanProof
