module

public import ConLeche.Model.Inductives.BlockTableMember
import ConLeche.Verify.Inductives.MutualWF
public section

/-!
# The projection-table stage over a block's members (task #315, M4 s5)

`mutualTables` (`ConLeche/Kernel/Inductives/MutualInstall.lean`) walks
the block's members in order; at a STRUCTURE-LIKE one (one
constructor, no index) it conses that member's projection table, and
at every other member it conses nothing (`mutualMemberTable_inv`).
This module folds the P step at ONE table — `BlockTableStep`, a
PROPOSITION here, proved elsewhere — over that walk.

The fold's only real work is the transport: a later member's table is
consed at an environment the earlier tables have already grown, so
each member's `TableMember` bundle must cross the OTHER members'
conses (`TableMember.cross`).  It does, because a table's bodies are
its own structure's constructor telescope with only its OWN
projections inserted (`noProjAt_structProjBodies`), so the block-wide
`NoProjEnv` bookkeeping survives the cons and the stored readings are
unchanged (`denoteMeta_cons_mono`); the table's leaf sits at a fresh
name, so every member's and constructor's leaf is untouched
(`acvalWith_ne`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal IndCaps ProjTable
  MutualBlock MutualFormerA MutualCtor projTableName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## A table's bodies mention only its own structure's projections

The bodies are the constructor telescope's domains with the parameters
replaced by `bvar`s and the earlier fields by `T.proj j (bvar 0)`
(`structProjBodies`), so an expression free of `T'.proj i` stays free
of it for every `T' ≠ T`.  This is what carries the block's
`NoProjEnv` invariant across another member's table cons. -/

omit [SetTheory V] in
/-- The default expression is a `bvar`. -/
theorem noProjAt_default {T : Name} {i : Nat} : Expr.NoProjAt T i (default : Expr) :=
  Expr.noProjAt_bvar

/-- Lifting preserves the absence of a slot's `.proj` nodes. -/
theorem noProjAt_liftLooseBVars {T : Name} {i : Nat} (n : Nat) :
    ∀ (c : Nat) (e : Expr), Expr.NoProjAt T i e →
      Expr.NoProjAt T i (Expr.liftLooseBVars n c e) := by
  intro c e
  induction e generalizing c with
  | bvar j => intro _; rw [Expr.liftLooseBVars]; split <;> simp
  | sort u => intro _; rw [Expr.liftLooseBVars]; simp
  | const n us => intro h; rw [Expr.liftLooseBVars]; exact h
  | fvar idx ty => intro h; rw [Expr.liftLooseBVars]; exact h
  | lit l => intro _; rw [Expr.liftLooseBVars]; simp
  | app f a ihf iha =>
    intro h
    rw [Expr.noProjAt_app] at h
    rw [Expr.liftLooseBVars, Expr.noProjAt_app]
    exact ⟨ihf c h.1, iha c h.2⟩
  | lam ty b m ihty ihb =>
    intro h
    rw [Expr.noProjAt_lam] at h
    rw [Expr.liftLooseBVars, Expr.noProjAt_lam]
    exact ⟨ihty c h.1, ihb (c + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro h
    rw [Expr.noProjAt_forallE] at h
    rw [Expr.liftLooseBVars, Expr.noProjAt_forallE]
    exact ⟨ihty c h.1, ihb (c + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro h
    rw [Expr.noProjAt_letE] at h
    rw [Expr.liftLooseBVars, Expr.noProjAt_letE]
    exact ⟨iht c h.1, ihval c h.2.1, ihb (c + 1) h.2.2⟩
  | proj s j e ihe =>
    intro h
    rw [Expr.noProjAt_proj] at h
    rw [Expr.liftLooseBVars, Expr.noProjAt_proj]
    exact ⟨h.1, ihe c h.2⟩

/-- Capture-avoiding instantiation preserves the absence of a slot's
`.proj` nodes. -/
theorem noProjAt_instantiate1Lift {T : Name} {i : Nat} {v : Expr}
    (hv : Expr.NoProjAt T i v) :
    ∀ (e : Expr) (d : Nat), Expr.NoProjAt T i e →
      Expr.NoProjAt T i (e.instantiate1Lift v d) := by
  intro e
  induction e with
  | bvar j =>
    intro d _
    rw [ConLeche.Expr.instantiate1Lift]
    split
    · exact noProjAt_liftLooseBVars _ _ _ hv
    · split <;> simp
  | sort u => intro d _; rw [ConLeche.Expr.instantiate1Lift]; simp
  | const n us => intro d h; rw [ConLeche.Expr.instantiate1Lift]; exact h
  | fvar idx ty => intro d h; rw [ConLeche.Expr.instantiate1Lift]; exact h
  | lit l => intro d _; rw [ConLeche.Expr.instantiate1Lift]; simp
  | app f a ihf iha =>
    intro d h
    rw [Expr.noProjAt_app] at h
    rw [ConLeche.Expr.instantiate1Lift, Expr.noProjAt_app]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam ty b m ihty ihb =>
    intro d h
    rw [Expr.noProjAt_lam] at h
    rw [ConLeche.Expr.instantiate1Lift, Expr.noProjAt_lam]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro d h
    rw [Expr.noProjAt_forallE] at h
    rw [ConLeche.Expr.instantiate1Lift, Expr.noProjAt_forallE]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d h
    rw [Expr.noProjAt_letE] at h
    rw [ConLeche.Expr.instantiate1Lift, Expr.noProjAt_letE]
    exact ⟨iht d h.1, ihval d h.2.1, ihb (d + 1) h.2.2⟩
  | proj s j e ihe =>
    intro d h
    rw [Expr.noProjAt_proj] at h
    rw [ConLeche.Expr.instantiate1Lift, Expr.noProjAt_proj]
    exact ⟨h.1, ihe d h.2⟩

/-- Peeling Π-binders at slot-free arguments preserves the absence. -/
theorem noProjAt_instPisAtLift {T : Name} {i : Nat} :
    ∀ (args : List Expr) (e r : Expr),
      (∀ a ∈ args, Expr.NoProjAt T i a) →
      ConLeche.Expr.instPisAtLift args e = some r →
      Expr.NoProjAt T i e → Expr.NoProjAt T i r
  | [], e, r, _, h, he => by
    simp only [ConLeche.Expr.instPisAtLift, Option.some.injEq] at h
    exact h ▸ he
  | a :: as, e, r, hall, h, he => by
    match e with
    | .forallE ty body mb =>
      rw [Expr.noProjAt_forallE] at he
      refine noProjAt_instPisAtLift as _ r (fun a' ha' => hall a' (List.mem_cons_of_mem _ ha'))
        h ?_
      exact noProjAt_instantiate1Lift (hall a List.mem_cons_self) body 0 he.2
    | .bvar _ | .sort _ | .const _ _ | .fvar _ _ | .app _ _ | .lam _ _ _ | .letE _ _ _
    | .lit _ | .proj _ _ _ => exact nomatch h

/-- The table-body generator inserts only its OWN structure's
projections. -/
theorem noProjAt_structProjBodiesGo {T T' : Name} {i : Nat} (hne : T' ≠ T) :
    ∀ (k i0 : Nat) (e : Expr) (l : List Expr),
      ConLeche.structProjBodiesGo T' k i0 e = some l →
      Expr.NoProjAt T i e → ∀ bd ∈ l, Expr.NoProjAt T i bd := by
  intro k
  induction k with
  | zero =>
    intro i0 e l h _
    simp only [ConLeche.structProjBodiesGo, Option.some.injEq] at h
    subst h
    intro bd hbd
    exact absurd hbd List.not_mem_nil
  | succ k ih =>
    intro i0 e l h he
    match e with
    | .forallE fdom body mb =>
      simp only [ConLeche.structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨l', hl', rfl⟩ := h
      rw [Expr.noProjAt_forallE] at he
      intro bd hbd
      rcases List.mem_cons.mp hbd with rfl | hbd
      · exact he.1
      · refine ih (i0 + 1) _ l' hl' ?_ bd hbd
        refine noProjAt_instantiate1Lift ?_ body 0 he.2
        rw [ConLeche.structProjArgP, Expr.noProjAt_proj]
        exact ⟨fun hh => hne hh.1, by simp⟩
    | .bvar _ | .sort _ | .const _ _ | .fvar _ _ | .app _ _ | .lam _ _ _ | .letE _ _ _
    | .lit _ | .proj _ _ _ => exact nomatch h

/-- **A table's bodies are free of any other structure's projections.** -/
theorem noProjAt_structProjBodies {T T' : Name} {i nP nF : Nat} {cty : Expr}
    {bodies : Array Expr} (hne : T' ≠ T)
    (h : ConLeche.structProjBodies T' nP nF cty = some bodies)
    (hcty : Expr.NoProjAt T i cty) :
    ∀ k, Expr.NoProjAt T i (bodies.getD k default) := by
  intro k
  unfold ConLeche.structProjBodies at h
  split at h
  · next r hr =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    have hall : ∀ bd ∈ l, Expr.NoProjAt T i bd :=
      noProjAt_structProjBodiesGo hne nF 0 r l hl
        (noProjAt_instPisAtLift (ConLeche.structProjPs nP) cty r
          (fun a ha => by
            obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
            simp) hr hcty)
    have hsz : (List.toArray l).size = l.length := rfl
    rw [Array.getD]
    split
    · next hk =>
      rw [hsz] at hk
      refine hall _ ?_
      show l[k]'hk ∈ l
      exact List.getElem_mem hk
    · exact noProjAt_default
  · exact nomatch h

/-! ## A member's table data crosses another member's table cons -/

/-- **A member's table data crosses another member's table cons.**
The head is a table of a DIFFERENT structure, so nothing it stores
mentions this member's slots: its type is a sort, and its bodies are
that structure's constructor telescope with only its OWN projections
inserted (`noProjAt_structProjBodies`).  The readings survive
(`denoteMeta_cons_mono`), the leaves are untouched (the table's name
is fresh, so it is neither the member's nor its constructor's). -/
theorem TableMember.cross {m : EnvModel V env} {lps : List Name} {nP : Nat} {T : Name}
    {cvTa cvCa : ConstantVal} {nF J : Nat} {resSort : Level} {isProp : Bool}
    {sorts : List Level} {pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {S : (Name → Nat) → (Nat → V) → V}
    (h : TableMember m lps nP T cvTa cvCa nF J resSort isProp sorts pps ds Es S)
    {tbl : ProjTable} {cty : Expr} {nF' : Nat}
    (hfresh : env.find? (ConstantInfo.projInfo tbl).name = none)
    (hbodies : ConLeche.structProjBodies tbl.structName nP nF' cty = some tbl.bodies)
    (hcty : ∃ ci ∈ env.consts, ci.toConstantVal.type = cty)
    (hnpT : ∀ i, NoProjEnv env tbl.structName i)
    (hne : tbl.structName ≠ T)
    (m₂ : EnvModel V ⟨.projInfo tbl :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0)) :
    TableMember m₂ lps nP T cvTa cvCa nF J resSort isProp sorts pps ds Es S := by
  -- the head's pieces mention no member's slots
  have hheadT : ∀ (T' : Name) (i : Nat), (∀ j, NoProjEnv env T' j) → T' ≠ tbl.structName →
      NoProjHead (.projInfo tbl) T' i := by
    intro T' i hnpT' hneT
    refine ⟨?_, (fun _ _ _ hh => nomatch hh), (fun _ _ _ _ hh => nomatch hh), ?_⟩
    · show Expr.NoProjAt T' i (.sort (.succ .zero))
      exact Expr.noProjAt_sort
    · intro tbl₂ heq k _
      obtain rfl := ConstantInfo.projInfo.inj heq
      obtain ⟨ci, hci, rfl⟩ := hcty
      exact noProjAt_structProjBodies (fun hh => hneT hh.symm) hbodies ((hnpT' i).type ci hci) k
  have hfT := h.fT
  have hfC := h.fC
  have hneT : T ≠ (ConstantInfo.projInfo tbl).name := by
    intro hh; rw [hh, hfresh] at hfT; exact nomatch hfT
  have hneC : cvCa.name ≠ (ConstantInfo.projInfo tbl).name := by
    intro hh; rw [hh, hfresh] at hfC; exact nomatch hfC
  have hacT : ∀ ψ : Name → Nat, m₂.acval T ψ = m.acval T ψ := by
    intro ψ; rw [hac, acvalWith_ne hneT]
  have hacC : ∀ ψ : Name → Nat, m₂.acval cvCa.name ψ = m.acval cvCa.name ψ := by
    intro ψ; rw [hac, acvalWith_ne hneC]
  have hbody : ∀ ψ : Name → Nat,
      ctorBodyAVI m₂ T nP nF ψ (Es ψ) = ctorBodyAVI m T nP nF ψ (Es ψ) := by
    intro ψ; unfold ctorBodyAVI; rw [hacT]
  have hcrossT : ConsCrossAt (.projInfo tbl) cvTa.type := by
    intro t2 he' j
    cases he'
    exact (hnpT j).type _ (ConLeche.Semantics.Env.find?_mem hfT)
  have hcrossC : ConsCrossAt (.projInfo tbl) cvCa.type := by
    intro t2 he' j
    cases he'
    exact (hnpT j).type _ (ConLeche.Semantics.Env.find?_mem hfC)
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (m.wf _ (ConLeche.Semantics.Env.find?_mem hfT)).2.2.1
  have hcbC : ConstsBound env cvCa.type :=
    constsBound_of_constsResolve _ (m.wf _ (ConLeche.Semantics.Env.find?_mem hfC)).2.2.1
  exact
    { nproj := fun j => (h.nproj j).cons (hheadT T j h.nproj (fun hh => hne hh.symm))
      fT := ConLeche.Env.find?_cons_of_fresh hfresh hfT
      lpsT := h.lpsT
      fC := ConLeche.Env.find?_cons_of_fresh hfresh hfC
      lpsC := h.lpsC
      stripC := h.stripC
      prop := h.prop
      Tshape := h.Tshape
      Cshape := h.Cshape
      resT := h.resT
      resR := h.resR
      resC := h.resC
      FD := h.FD.cross hfresh hcrossT hcbT m₂ hac
      CDread := fun ψ => by
        rw [hbody, hac]
        exact denoteMeta_cons_mono hfresh hcrossC ψ 0 hcbC (h.CDread ψ)
      CDlen := h.CDlen
      CDbelow := h.CDbelow
      CDbits := h.CDbits
      leq := h.leq
      Tmem := fun ψ ρ => by rw [hacT]; exact h.Tmem ψ ρ
      Cmem := fun ψ ρ => by rw [hacC, hbody]; exact h.Cmem ψ ρ
      fold := fun ψ ρ ts hsp => by rw [hacT]; exact h.fold ψ ρ ts hsp
      fib := h.fib
      ctor := fun ψ ρ as fs ha hf => by rw [hacC]; exact h.ctor ψ ρ as fs ha hf
      iff := h.iff
      fields := h.fields
      boundP := h.boundP
      sortsF := h.sortsF }

/-- **A member's table data crosses another member's table cons**, the
per-member wrapper (`TableMember.cross`). -/
theorem MemberTableOk.cross {m : EnvModel V env} {b : MutualBlock}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} {isProp : Bool}
    {S : Nat → (Name → Nat) → (Nat → V) → V} {f : MutualFormerA} {mIdx : Nat}
    (h : MemberTableOk m b ctorsA sortss isProp S f mIdx)
    {tbl : ProjTable} {cty : Expr} {nF' : Nat}
    (hfresh : env.find? (ConstantInfo.projInfo tbl).name = none)
    (hbodies : ConLeche.structProjBodies tbl.structName b.nP nF' cty = some tbl.bodies)
    (hcty : ∃ ci ∈ env.consts, ci.toConstantVal.type = cty)
    (hnpT : ∀ i, NoProjEnv env tbl.structName i)
    (hne : tbl.structName ≠ f.cvTa.name)
    (m₂ : EnvModel V ⟨.projInfo tbl :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0)) :
    MemberTableOk m₂ b ctorsA sortss isProp S f mIdx := by
  intro J c hown hnIdx
  obtain ⟨pps, ds, Es, hCname, hnF, hTM⟩ := h J c hown hnIdx
  exact ⟨pps, ds, Es, hCname, hnF, hTM.cross hfresh hbodies hcty hnpT hne m₂ hac⟩

/-! ## The fold over the members -/

/-- **The table stage over the members**: each member either conses
nothing or conses its projection table (`mutualMemberTable_inv`); the
carrier survives every cons (the P step `BlockTableStep`), and the
leaves off the block's table names are untouched. -/
theorem stageBlockTablesGo (step : BlockTableStep V μ) {b : MutualBlock}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} {isProp : Bool}
    {S : Nat → (Name → Nat) → (Nat → V) → V} :
    ∀ (l : List (MutualFormerA × Nat)) {env : Env} (mp : EnvModelM V μ env) {env' : Env},
      ConLeche.mutualTables (m := ConLeche.CheckM) b ctorsA sortss l env = .ok env' →
      (l.map (·.1.cvTa.name)).Nodup →
      (∀ p ∈ l, MemberTableOk mp.base2 b ctorsA sortss isProp S p.1 p.2) →
      ∃ mp' : EnvModelM V μ env',
        ∀ n : Name, (∀ p ∈ l, n ≠ projTableName p.1.cvTa.name) →
          mp'.base2.acval n = mp.base2.acval n := by
  intro l
  induction l with
  | nil =>
    intro env mp env' h _ _
    obtain rfl := ConLeche.mutualTables_nil_inv h
    exact ⟨mp, fun _ _ => rfl⟩
  | cons p rest ih =>
    intro env mp env' h hnd hmem
    obtain ⟨f, mIdx⟩ := p
    obtain ⟨envI, hI, hrestRun⟩ := ConLeche.mutualTables_inv h
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases ConLeche.mutualMemberTable_inv hI with rfl | ⟨J, c, hown, hnIdx, htbl⟩
    · -- the member conses nothing
      obtain ⟨mp', hoff⟩ := ih mp hrestRun hnd.2 (fun q hq => hmem q (List.mem_cons_of_mem _ hq))
      exact ⟨mp', fun n hn => hoff n (fun q hq => hn q (List.mem_cons_of_mem _ hq))⟩
    · -- the member conses its table
      obtain ⟨pps, ds, Es, hCname, -, hTM⟩ := hmem (f, mIdx) List.mem_cons_self J c hown hnIdx
      rw [← hCname] at htbl
      obtain ⟨bodies, hbodies, -, -, hfreshTbl, rfl⟩ := ConLeche.checkStructProjTable_inv htbl
      obtain ⟨mpI, hacI⟩ := step mp hTM htbl
      have hmemI : ∀ q ∈ rest, MemberTableOk mpI.base2 b ctorsA sortss isProp S q.1 q.2 := by
        intro q hq
        refine (hmem q (List.mem_cons_of_mem _ hq)).cross (nF' := c.nF)
          (cty := (ctorsA.getD J default).1.type)
          (tbl := ⟨f.cvTa.name, b.lps, b.nP, (ctorsA.getD J default).1.name, c.nF, f.s, bodies,
            ConLeche.structProjGuards (ctorsA.getD J default).1.type b.nP c.nF (sortss.getD J []),
            1⟩)
          hfreshTbl hbodies ⟨.ctorInfo (ctorsA.getD J default).1 b.nP c.nF,
            ConLeche.Semantics.Env.find?_mem hTM.fC, rfl⟩ hTM.nproj ?_ mpI.base2 hacI
        intro hh
        refine hnd.1 ?_
        show f.cvTa.name ∈ rest.map (·.1.cvTa.name)
        rw [show f.cvTa.name = q.1.cvTa.name from hh]
        exact List.mem_map_of_mem hq
      obtain ⟨mp', hoff⟩ := ih mpI hrestRun hnd.2 hmemI
      refine ⟨mp', fun n hn => ?_⟩
      rw [hoff n (fun q hq => hn q (List.mem_cons_of_mem _ hq)), hacI,
        acvalWith_ne (hn (f, mIdx) List.mem_cons_self)]

/-- **The table stage**: the run's final environment carries an
`EnvModelM` whose carrier agrees with the one it started from off the
block's table names (`stageBlockTablesGo`). -/
theorem stageBlockTables (step : BlockTableStep V μ) {b : MutualBlock}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} {isProp : Bool}
    {S : Nat → (Name → Nat) → (Nat → V) → V} {fms : List MutualFormerA} {env env' : Env}
    (mp : EnvModelM V μ env)
    (hrun : ConLeche.mutualTables (m := ConLeche.CheckM) b ctorsA sortss fms.zipIdx env = .ok env')
    (hnd : (fms.map (·.cvTa.name)).Nodup)
    (hmem : ∀ p ∈ fms.zipIdx, MemberTableOk mp.base2 b ctorsA sortss isProp S p.1 p.2) :
    Nonempty (EnvModelM V μ env') := by
  have hnd' : ((fms.zipIdx).map (·.1.cvTa.name)).Nodup := by
    rw [show fms.zipIdx.map (·.1.cvTa.name) = fms.map (·.cvTa.name) from by
      rw [show (fun x : MutualFormerA × Nat => x.1.cvTa.name)
        = (fun f : MutualFormerA => f.cvTa.name) ∘ Prod.fst from rfl, ← List.map_map,
        List.zipIdx_map_fst]]
    exact hnd
  obtain ⟨mp', -⟩ := stageBlockTablesGo step fms.zipIdx mp hrun hnd' hmem
  exact ⟨mp'⟩

end ConLeche.Model
