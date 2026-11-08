module

public import InLeanProof.TailSim
public import InLeanProof.DivModArm
public import InLeanProof.BlockPresR
import ConLeche.Semantics.Bridge.Sound
public import ConLeche.Model.Fold
import ConLeche.Model.Capstone
import ConLeche.Model.Inductives.BlockRunFacts
import ConLeche.Verify.Inductives.BlockShapeInv
import all Lean.Declaration

/-!
# The simulation theorem proved (task #451, lane P4)

The relation between the kernel environment and con-leche's (`EnvRel`), the
statement (`AddDeclSound`) and its proof `addDeclSound`: InLean's `addDecl` at
`theoremConfig` accepting a safe declaration that is not a non-standard axiom
keeps the relation and the environment's model.  The step, by kind:

* **master's side**: InLean's check accepted ⇒ master's pure fueled step
  accepts the records of what InLean adds (O6, `checkDecl_sim_nk`; O7,
  `checkIndDeclC_sim`) ⇒ master's fold carries `EnvModelOk` (`foldPM`), and
  master's accepted step installs exactly the records' constants and tables
  (`checkDecl_env`, from the run relation), so the new environment extends
  the old one;
* **the relation**: InLean's reading of the environment (`EnvPresI`) and the
  projection bodies' range (`ProjBodiesInRange`) are kept by the per-kind
  lemmas (`presI_*`, `quotGroupPres`, `indGroupPresBP`;
  `projBodiesInRange_*`).
-/

public section

namespace InLeanProof

variable {lim : InLean.Limits}

open Lean InLean

/-! ## Master's accepted step installs the records -/

/-- **What master's accepted step returns**: the environment with the
record's constants and tables pushed (`declConstants`, `declTables`), read
off the run relation (`checkDeclRun_ofEnvFactsK`). -/
theorem checkDecl_env {pins : List ConLeche.NatOpPinSet} {F : Nat} {L L' : ConLeche.Env}
    {d : ConLeche.Declaration}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins L d = .ok L') :
    L' = L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d) := by
  obtain ⟨-, hr⟩ := ConLeche.Semantics.checkDeclRun_ofEnvFactsK h
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, hvf, rfl, -⟩ := hr
    obtain ⟨-, -, -, -, rfl, -⟩ := hcv
    obtain ⟨-, -, rfl, -⟩ := hvf
    cases cv; rfl
  | thmDecl cv value =>
    obtain ⟨-, type', value', hcv, -, -, rfl⟩ := hr
    obtain ⟨-, -, -, -, rfl, -⟩ := hcv
    cases cv; rfl
  | opaqueDecl cv value =>
    obtain ⟨-, type', value', hcv, -, rfl, -⟩ := hr
    obtain ⟨-, -, -, -, rfl, -⟩ := hcv
    cases cv; rfl
  | axiomDecl cv =>
    rcases hr with ⟨hq, -, -, -, rfl⟩ | ⟨hq, type', -, hcv, hb⟩
    · simp only [ConLeche.declConstants, ConLeche.declTables, hq, ↓reduceIte]; rfl
    · obtain ⟨-, -, -, -, rfl, -⟩ := hcv
      have hcv' : (⟨cv.name, cv.levelParams, cv.type⟩ : ConLeche.ConstantVal) = cv := by cases cv; rfl
      simp only [hcv'] at hb
      rcases hb with ⟨hs, rfl⟩ | ⟨ht, -, rfl⟩ | ⟨ht, -, rfl⟩ | ⟨-, -, -, -, -, -, hs, rfl⟩
      · have : cv.name ≠ ConLeche.sorryAxName := by
          intro h'
          rw [ConLeche.stdAxiomOk, ite_eq_right, ite_eq_right] at hs <;> rw [h'] at * <;>
            first | exact absurd hs (by decide) | decide
        simp only [ConLeche.declConstants, ConLeche.declTables, hq, this, ↓reduceIte]; rfl
      · have : cv.name ≠ ConLeche.sorryAxName := by rw [ht]; decide
        simp only [ConLeche.declConstants, ConLeche.declTables, hq, this, ↓reduceIte]; rfl
      · have : cv.name ≠ ConLeche.sorryAxName := by rcases ht with ht | ht <;> rw [ht] <;> decide
        simp only [ConLeche.declConstants, ConLeche.declTables, hq, this, ↓reduceIte]; rfl
      · simp only [ConLeche.declConstants, ConLeche.declTables, hs, ↓reduceIte]; rfl
  | quotDecl k cv =>
    obtain ⟨-, -, -, rfl⟩ := hr
    rfl
  | indDecl block nP =>
    have hr' : ConLeche.Semantics.DeclIndRunDispatchK F L block nP L' := hr
    unfold ConLeche.Semantics.DeclIndRunDispatchK at hr'
    cases hdf : ConLeche.readBlock nP block with
    | error e => rw [hdf] at hr'; exact hr'.elim
    | ok p =>
      rw [hdf] at hr'
      simp only [ConLeche.declConstants, ConLeche.declTables, hdf]
      exact ConLeche.Semantics.blockRun_env (ConLeche.readBlock_declared hdf) hr'

/-- **Master's accepted fold installs the records, in order.** -/
theorem foldlM_checkDecl_env {pins : List ConLeche.NatOpPinSet} {F : Nat} :
    ∀ (ds : List ConLeche.Declaration) (L : ConLeche.Env) {L' : ConLeche.Env},
      ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) L = .ok L' →
      L' = ds.foldl (fun L d => L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d)) L
  | [], _, _, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | d :: ds, L, _, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins L d with
    | error e => rw [hd] at h; exact nomatch h
    | ok L1 =>
      rw [hd] at h
      rw [List.foldl_cons, ← checkDecl_env hd]
      exact foldlM_checkDecl_env ds L1 h

end InLeanProof

namespace InLeanProof

variable {lim : InLean.Limits}

open Lean InLean

/-! ## InLean's side: the entry point and the kinds' shapes -/

/-- **InLean's accepted declaration check, inverted**: the kind's check at the
fresh state, the reserved names' check, no squatter at `sorryAx`'s name. -/
theorem checkDecl_run {E : Kernel.Environment} {decl : Declaration} {a : InLean.Added}
    (h : InLean.checkDecl (theoremConfig lim) E decl = .ok a) :
    ∃ s', InLean.checkDeclKindC .verified (theoremConfig lim) { env := E, coreAxioms := false, limits := lim } decl
        {} = .ok (a, s') ∧ InLean.basisNamesOk decl a = true ∧
      ∀ ci ∈ a.consts.toList, InLean.sorryAxSquat ci = false := by
  unfold InLean.checkDecl at h
  split at h
  · exact nomatch h
  unfold InLean.runC at h
  dsimp only at h
  split at h
  · rename_i a' s' hrun
    cases h
    obtain ⟨b, s₁, hKr, hT⟩ := bindI_ok hrun
    have hnb : InLean.basisNamesOk decl b = true := by
      cases hc : InLean.basisNamesOk decl b
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hT
        exact (throw_bindI_ok hT).elim
      · rfl
    simp only [hnb, ↓reduceIte] at hT
    split at hT
    · exact (throw_bindI_ok hT).elim
    · rename_i hc
      obtain ⟨rfl, -⟩ := pureI_ok hT
      refine ⟨s₁, hKr, hnb, ?_⟩
      have hc' : b.consts.any InLean.sorryAxSquat = false := by
        simpa [show (theoremConfig lim).coreAxioms = false from rfl] using hc
      simp only [← Array.any_toList, List.any_eq_false] at hc'
      exact fun ci hci => by simpa using hc' ci hci
  · exact nomatch h

theorem thm_shape {fe : InLean.FEnv} {v : TheoremVal} {a : InLean.Added} {s s' : InLean.CState}
    (h : InLean.checkThmC .verified fe v s = .ok (a, s')) :
    a = { consts := #[.thmInfo v] } ∧ fe.env.find? v.name = none := by
  unfold InLean.checkThmC at h
  obtain ⟨_, _, h1, h⟩ := bindI_ok h
  refine ⟨?_, checkConstantValC_fresh h1⟩
  obtain ⟨_, _, -, h⟩ := bindI_ok h
  obtain ⟨_, _, -, h⟩ := bindI_ok h
  obtain ⟨_, _, -, h⟩ := bindI_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, -, h⟩ := bindI_ok h
    exact (pureI_ok h).1.symm
  · exact (throw_bindI_ok h).elim

theorem opaque_shape {fe : InLean.FEnv} {v : OpaqueVal} {a : InLean.Added} {s s' : InLean.CState}
    (h : InLean.checkOpaqueC .verified fe v s = .ok (a, s')) :
    a = { consts := #[.opaqueInfo v] } ∧ fe.env.find? v.name = none := by
  unfold InLean.checkOpaqueC at h
  obtain ⟨_, _, h1, h⟩ := bindI_ok h
  refine ⟨?_, checkConstantValC_fresh h1⟩
  repeat' (first | exact (throw_bindI_ok h).elim | (obtain ⟨_, _, -, h⟩ := bindI_ok h) |
    (dsimp only at h; split at h))
  all_goals first | exact (pureI_ok h).1.symm | exact (throwI_ok h).elim

theorem defn_shape {fe : InLean.FEnv} {v : DefinitionVal} {a : InLean.Added} {s s' : InLean.CState}
    (hsafe : v.safety = .safe)
    (h : InLean.checkDefnC .verified (theoremConfig lim) fe v s = .ok (a, s')) :
    a = { consts := #[.defnInfo v] } ∧ fe.env.find? v.name = none := by
  unfold InLean.checkDefnC at h
  simp only [hsafe, show (DefinitionSafety.safe == DefinitionSafety.unsafe) = false from rfl,
    show (theoremConfig lim).uncertifiedNatOps = false from rfl,
    Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨_, _, h1, h⟩ := bindI_ok h
  refine ⟨?_, checkConstantValC_fresh h1⟩
  obtain ⟨_, _, -, h⟩ := bindI_ok h
  by_cases hc : (natOpNames.contains v.name || natDivModNames.contains v.name) = true
  · simp only [hc, ↓reduceIte] at h
    obtain ⟨_, _, -, h⟩ := bindI_ok h
    exact (pureI_ok h).1.symm
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    exact (pureI_ok h).1.symm

theorem axiom_shape {fe : InLean.FEnv} {v : AxiomVal} {a : InLean.Added} {s s' : InLean.CState}
    (h : InLean.checkAxiomC .verified (theoremConfig lim) fe v s = .ok (a, s')) :
    a = { consts := #[.axiomInfo v] } ∧ fe.env.find? v.name = none := by
  by_cases hq : v.name = InLean.quotSoundName
  · obtain ⟨h1, -, h3⟩ := checkAxiomC_quotSound h hq
    have : a.quot = false := by
      unfold InLean.checkAxiomC at h
      simp only [hq, beq_self_eq_true, ↓reduceIte] at h
      repeat' (first | exact (throw_bindI_ok h).elim | (obtain ⟨_, _, -, h⟩ := bindI_ok h) |
        split at h)
      all_goals first | (rw [← (pureI_ok h).1]) | exact (throwI_ok h).elim
    exact ⟨by cases a; simp_all, h3⟩
  · unfold InLean.checkAxiomC at h
    have bq : (v.name == InLean.quotSoundName) = false := by simpa using hq
    simp only [bq, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, _, h1, h⟩ := bindI_ok h
    refine ⟨?_, by have := checkConstantValC_fresh h1; exact this⟩
    repeat' (first | exact (throw_bindI_ok h).elim | exact (pureI_ok h).1.symm |
      exact (throwI_ok h).elim | split at h)

/-! ## The relation -/

/-- **The kernel environment `E` against con-leche's `L`**, at the theorem's
configuration (InLean's view `{ env := E, coreAxioms := false }`): InLean
finds a constant at a name exactly where `L` does, the two entries related
(their name, levels and type, and what InLean reads at use: values,
capabilities, firing modes), and the projection tables alike (`EnvPresI`);
and every projection body InLean builds off `E` is in range
(`ProjBodiesInRange`; a structure's bodies may leave the range while its
types are in it).  The simulation
of InLean's checks by con-leche's needs both.  It holds where InLean finds
nothing (`envRel_of_none`), every accepted step keeps it (`addDeclSound`),
and through it every safe constant of `E` but `sorryAx` reads as a constant
of `L` (`EnvRel.reads`). -/
structure EnvRel (E : Kernel.Environment) (L : ConLeche.Env) : Prop where
  pres : EnvPresI { env := E, coreAxioms := false } L
  proj : ProjBodiesInRange { env := E, coreAxioms := false }

/-- **The start**: an environment InLean finds nothing in is related to the
empty one. -/
theorem envRel_of_none {E : Kernel.Environment}
    (h : ∀ n, ({ env := E, coreAxioms := false } : InLean.FEnv).find? n = none) :
    EnvRel E ConLeche.Env.empty := by
  refine ⟨presI_empty h, projBodiesInRange_of_none fun T i => ?_⟩
  unfold InLean.FEnv.findProj?
  rw [h T]

/-- The projection reads at two environments storing alike. -/
theorem findProj_congr {fe : InLean.FEnv} {E' : Kernel.Environment}
    (h : ∀ n, E'.find? n = fe.env.find? n) (T : Name) (i : Nat) :
    ({ fe with env := E' } : InLean.FEnv).findProj? T i = fe.findProj? T i := by
  have hf : ∀ n, ({ fe with env := E' } : InLean.FEnv).find? n = fe.find? n :=
    fun n => FEnv.find?_congr (fe := fe) (fe' := { fe with env := E' }) rfl rfl (h n)
  unfold InLean.FEnv.findProj?
  rw [hf T]
  cases fe.find? T with
  | none => rfl
  | some ci =>
    cases ci with
    | inductInfo v =>
      show (if fe.isPending v.name = true then none else _) =
        (if fe.isPending v.name = true then none else _)
      split
      · rfl
      · split
        · split
          · rw [hf]
          · rfl
        · rfl
    | _ => rfl

theorem projBodiesInRange_congr {fe : InLean.FEnv} {E' : Kernel.Environment}
    (h : ∀ n, E'.find? n = fe.env.find? n) (hR : ProjBodiesInRange fe) :
    ProjBodiesInRange { fe with env := E' } := by
  intro T i e he
  rw [findProj_congr h] at he
  exact hR T i e he

/-- **Every safe constant of `E` but `sorryAx` reads as a constant of `L`**,
by name and type. -/
theorem EnvRel.reads {E : Kernel.Environment} {L : ConLeche.Env} (hR : EnvRel E L)
    {n : Name} {ci : Lean.ConstantInfo} (hf : E.find? n = some ci) (hsafe : SafeConst ci)
    (hn : n ≠ InLean.sorryAxName) :
    ∃ c ∈ L.consts, toName n = c.name ∧ toExprC ci.type = some c.toConstantVal.type := by
  have hs : InLean.safeConst ci = true := by
    cases ci <;> simp_all [SafeConst, InLean.safeConst]
  have hsee : ({ env := E, coreAxioms := false } : InLean.FEnv).sees n ci = true :=
    sees_safe hs fun h => absurd h hn
  have hfe : ({ env := E, coreAxioms := false } : InLean.FEnv).find? n = some ci := by
    rw [FEnv.find?_eq_filter]
    simp only [hf, Option.filter_some, hsee, ↓reduceIte]
  obtain ⟨cci, hL, hr⟩ := hR.pres.entry n ci hfe
  have hcv := hr.cv
  unfold ConLeche.Env.find? at hL
  have hmem := List.mem_of_find?_eq_some hL
  have hname := List.find?_some hL
  refine ⟨cci, hmem, ?_, ?_⟩
  · simp only [beq_iff_eq] at hname
    exact hname.symm
  · rw [ci_cv_type]; exact hcv.2.2.2.2

/-! ## One step, generically -/

theorem foldl_pushDelta_consts : ∀ (ds : List ConLeche.Declaration) (L : ConLeche.Env),
    ∃ new, (ds.foldl (fun L d => L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d))
      L).consts = new ++ L.consts
  | [], _ => ⟨[], rfl⟩
  | d :: ds, L => by
    obtain ⟨new, h⟩ := foldl_pushDelta_consts ds
      (L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d))
    refine ⟨new ++ (ConLeche.declConstants d).reverse, ?_⟩
    rw [List.foldl_cons, h]
    simp [ConLeche.Env.pushDelta]

universe w

/-- **A step whose records `ds` master's fold accepts** keeps the theorem's
invariants, given the relation at the new environment. -/
theorem step_of {V : Type w} [ConLeche.SetTheory V] {pins : List ConLeche.NatOpPinSet}
    {E' : Kernel.Environment} {L : ConLeche.Env}
    {ds : List ConLeche.Declaration} {F : Nat} {L₁ : ConLeche.Env}
    (hM : ConLeche.Model.EnvModelOk V L)
    (hfold : ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) L =
      .ok L₁)
    (hrel : EnvRel E' L₁) :
    ∃ L', EnvRel E' L' ∧ ConLeche.Model.EnvModelOk V L' ∧
      ∃ new, L'.consts = new ++ L.consts := by
  refine ⟨L₁, hrel, ConLeche.Model.foldPM ds L hM hfold, ?_⟩
  rw [foldlM_checkDecl_env ds L hfold]
  exact foldl_pushDelta_consts ds L

/-! ## The one-constant kinds -/

theorem natKinds_of_modelOk {V : Type w} [ConLeche.SetTheory V] {L : ConLeche.Env}
    (h : ConLeche.Model.EnvModelOk V L) : ConLeche.NatKinds L :=
  h.1.elim fun mp _ => mp.base2.basis_pinned.natKinds

/-- The relation's view under any limits. -/
theorem EnvRel.presL {E : Kernel.Environment} {L : ConLeche.Env} (hR : EnvRel E L) :
    EnvPresI { env := E, coreAxioms := false, limits := lim } L :=
  presI_congr hR.pres rfl rfl rfl (fun _ => rfl)

/-- The projection reads do not depend on the limits. -/
theorem findProj_limits (fe : InLean.FEnv) (lim : InLean.Limits) (T : Name) (i : Nat) :
    ({ fe with limits := lim } : InLean.FEnv).findProj? T i = fe.findProj? T i := rfl

/-- The projection bodies' range at two views reading the same tables. -/
theorem projBodiesInRange_of_findProj {fe fe' : InLean.FEnv}
    (h : ∀ T i, fe'.findProj? T i = fe.findProj? T i) (hR : ProjBodiesInRange fe) :
    ProjBodiesInRange fe' :=
  fun T i e he => hR T i e ((h T i) ▸ he)

/-- The relation's projection range under any limits. -/
theorem EnvRel.projL {E : Kernel.Environment} {L : ConLeche.Env} (hR : EnvRel E L) :
    ProjBodiesInRange { env := E, coreAxioms := false, limits := lim } :=
  projBodiesInRange_of_findProj (findProj_limits { env := E, coreAxioms := false } lim) hR.proj

/-- The job's premises at the relation's view under any limits. -/
theorem jobEnvI_of {V : Type w} [ConLeche.SetTheory V] (hlaws : EnvLaws) {E : Kernel.Environment}
    {L : ConLeche.Env} (hR : EnvRel E L) (hM : ConLeche.Model.EnvModelOk V L) :
    JobEnvI { env := E, coreAxioms := false, limits := lim } L :=
  ⟨hlaws, hR.presL, envWF_of_modelOk hM,
    hR.projL⟩

/-- **A declaration adding one constant** (every kind but the quotient package
and an inductive block). -/
theorem single_step {V : Type w} [ConLeche.SetTheory V] (hlaws : EnvLaws)
    {E : Kernel.Environment} {L : ConLeche.Env} {decl : Declaration} {a : InLean.Added}
    {ci : Lean.ConstantInfo}
    (hd : SafeDecl decl) (hdr : DeclRangeOk decl) (hnI : ∀ lps nP ts u, decl ≠ .inductDecl lps nP ts u)
    (ha : InLean.checkDecl (theoremConfig lim) E decl = .ok a) (hac : a = { consts := #[ci] })
    (hfresh : E.find? ci.name = none) (hnotInd : ∀ v, ci ≠ .inductInfo v)
    (hR : EnvRel E L) (hM : ConLeche.Model.EnvModelOk V L)
    (hpres : ∀ d, toDecl [ci] = some d → EnvPresI { env := InLean.addConst E ci, coreAxioms := false }
      (L.pushDelta (ConLeche.declConstants d) (ConLeche.declTables d))) :
    ∃ L', EnvRel (InLean.addConst E ci) L' ∧
      ConLeche.Model.EnvModelOk V L' ∧ ∃ new, L'.consts = new ++ L.consts := by
  obtain ⟨-, ds, hds, F, L₁, hfold⟩ :=
    checkDecl_sim_nk (jobEnvI_of hlaws hR hM) (natKinds_of_modelOk hM) hd hdr hnI ha
  subst hac
  have hds' : ds.length = 1 ∧ ∀ d ∈ ds, toDecl [ci] = some d := by
    simp only [List.mapM_cons, List.mapM_nil, Option.pure_def,
      Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hds
    obtain ⟨d, hd1, _, rfl, rfl⟩ := hds
    simp [hd1]
  obtain ⟨d, rfl⟩ : ∃ d, ds = [d] := by
    match ds, hds'.1 with
    | [d], _ => exact ⟨d, rfl⟩
  have hd' := hds'.2 d (List.mem_singleton_self d)
  have hL₁ := foldlM_checkDecl_env [d] L hfold
  have hrel : EnvRel (InLean.addConst E ci) L₁ := by
    rw [hL₁]
    exact ⟨hpres d hd', projBodiesInRange_one hlaws hR.proj (ctorsStored_of_pres hR.pres) hfresh
      hnotInd⟩
  exact step_of hM hfold hrel

/-! ## The inductive block -/

/-- **The declared parameter count is the stored first former's**: an
accepted block check compared every former entry's `numParams` with the
shape's, which is the declared count (`genEntriesAgree`). -/
theorem numParams_of_checkIndDeclC {fe : InLean.FEnv} {block : List Lean.ConstantInfo} {nP : Nat}
    {s s' : CState} (h : InLean.checkIndDeclC .verified fe block nP s = .ok ((), s'))
    {v : InductiveVal} {rest : List Lean.ConstantInfo} (hb : block = .inductInfo v :: rest) :
    v.numParams = nP := by
  unfold InLean.checkIndDeclC at h
  split at h
  · cases hp : InLean.readBlock nP block with
    | error e => rw [hp] at h; exact (throwI_ok h).elim
    | ok p =>
      rw [hp] at h
      obtain ⟨_, _, h1, h2⟩ := bindI_ok h
      obtain ⟨cvTs, cs, rs, hsp, hlen, -⟩ := checkBlockKS_cover h2
      obtain ⟨cvT0, tl, cs', rs', nIdxs, hsp', hnP, hmem, -, -⟩ := readBlock_spec hp
      rw [hsp] at hsp'
      obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj hsp')
      obtain ⟨v', rest', hb', hv'⟩ := blockSplit_head hsp
      rw [hb] at hb'
      obtain ⟨hvv, -⟩ := List.cons.inj hb'
      cases hvv
      obtain ⟨ms, hms, hcvT⟩ : ∃ ms ∈ p.members, ms.cvT = cvT0 := by
        rw [hmem]
        cases nIdxs with
        | nil => rw [hmem] at hlen; simp [mkMembers] at hlen
        | cons n0 nr =>
          cases hgr : blockGroups ((cvT0 :: tl).map (·.name)) cvT0.levelParams nP
              (cvT0 :: tl).length (cs.map fun c => (c.1, c.2.2)) with
          | nil => rw [hmem, hgr] at hlen; simp [mkMembers] at hlen
          | cons g0 gr => exact ⟨{ cvT := cvT0, declared := cvT0, nIdx := n0, ctors := g0 },
              by simp [mkMembers], rfl⟩
      obtain ⟨v'', hf, hn, -⟩ := genEntriesAgree_members h1 ms hms
      rw [hcvT, hb] at hf
      have hname : (Lean.ConstantInfo.inductInfo v).name = cvT0.name := by
        rw [← hv']; rfl
      simp only [InLean.constNamed?, List.find?_cons, hname, beq_self_eq_true,
        Option.some.injEq] at hf
      cases hf
      rw [hn, hnP]
  · exact (throwI_ok h).elim

/-! ## The quotient package -/

theorem quotConstsI_nodup : (quotConstsI.toList.map (·.name)).Nodup := by
  rw [quotConstsI_eq]
  exact List.Pairwise.of_map (S := fun a b => a ≠ b) toName
    (fun _ _ h e => h (congrArg toName e)) (by decide)

/-- **The quotient package's step.** -/
theorem quot_step {V : Type w} [ConLeche.SetTheory V] (hlaws : EnvLaws)
    {E : Kernel.Environment} {L : ConLeche.Env} {a : InLean.Added}
    (ha : InLean.checkDecl (theoremConfig lim) E .quotDecl = .ok a)
    (hR : EnvRel E L) (hM : ConLeche.Model.EnvModelOk V L) :
    a.quot = true ∧ ∃ L', EnvRel (InLean.markQuot (a.consts.foldl InLean.addConst E)) L' ∧
      ConLeche.Model.EnvModelOk V L' ∧ ∃ new, L'.consts = new ++ L.consts := by
  obtain ⟨s', hK, -, -⟩ := checkDecl_run ha
  obtain ⟨-, ds, hds, F, L₁, hfold⟩ :=
    checkDecl_sim_nk (decl := .quotDecl) (jobEnvI_of hlaws hR hM) (natKinds_of_modelOk hM) trivial trivial
      (fun _ _ _ _ h => by cases h) ha
  have hpres := quotGroupPres hlaws _ L {} s' a ds hR.presL hK hds
  obtain ⟨-, h1, h2, h3, h4, rfl, -⟩ := checkQuotC_run hK
  refine ⟨rfl, ?_⟩
  have hfresh : ∀ ci ∈ quotConstsI.toList, E.find? ci.name = none := by
    rw [quotConstsI_eq]
    intro ci hci
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
    rcases hci with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hE' : ∀ n, (InLean.markQuot (quotConstsI.foldl InLean.addConst E)).find? n =
      (quotConstsI.toList.foldl InLean.addConst E).find? n := by
    intro n; rw [markQuot_find hlaws, ← Array.foldl_toList]
  have hff := find_foldl_addConst hlaws _ E hfresh quotConstsI_nodup
  have hgrp := projBodiesInRange_group (fe := { env := E, coreAxioms := false }) hlaws hR.proj
    (ctorsStored_of_pres hR.pres) hfresh quotConstsI_nodup (fun ci hci => by
      apply projBodiesInRange_notInd
      intro v hv
      have := FEnv.env_of_find hv
      rw [show ({ env := E, coreAxioms := false } : InLean.FEnv).env = E from rfl,
        hff.1 ci hci] at this
      rw [quotConstsI_eq] at hci
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hci
      rcases hci with rfl | rfl | rfl | rfl <;> cases this)
  have hrel : EnvRel (InLean.markQuot (quotConstsI.foldl InLean.addConst E)) L₁ := by
    rw [foldlM_checkDecl_env ds L hfold]
    refine ⟨presI_congr hpres rfl rfl rfl (fun _ => rfl), ?_⟩
    exact projBodiesInRange_congr (E' := InLean.markQuot (quotConstsI.foldl InLean.addConst E))
      (fun n => hE' n) hgrp
  exact step_of hM hfold hrel

/-- An accepted block check's block starts with a former. -/
theorem checkIndDeclC_head {fe : InLean.FEnv} {block : List Lean.ConstantInfo} {nP : Nat}
    {s s' : CState} (h : InLean.checkIndDeclC .verified fe block nP s = .ok ((), s')) :
    ∃ v rest, block = .inductInfo v :: rest := by
  unfold InLean.checkIndDeclC at h
  split at h
  · cases hp : InLean.readBlock nP block with
    | error e => rw [hp] at h; exact (throwI_ok h).elim
    | ok p =>
      obtain ⟨cvT0, tl, cs', rs', nIdxs, hsp, -⟩ := readBlock_spec hp
      obtain ⟨v, rest, hb, -⟩ := blockSplit_head hsp
      exact ⟨v, rest, hb⟩
  · exact (throwI_ok h).elim

/-- A constant's terms carry no free variable and no metavariable (the cached
flags). -/
@[expose] def CIGround : Lean.ConstantInfo → Prop
  | .recInfo v => (v.type.hasFVar = false ∧ v.type.hasMVar = false) ∧
      ∀ r ∈ v.rules, r.rhs.hasFVar = false ∧ r.rhs.hasMVar = false
  | ci => ci.type.hasFVar = false ∧ ci.type.hasMVar = false

/-- What `checkInductiveC` tests of each generated constant (`constGround`). -/
theorem CIGround_of_constGround {ci : Lean.ConstantInfo} (h : InLean.constGround ci = true) :
    CIGround ci := by
  cases ci <;> simp_all [InLean.constGround, CIGround]

theorem okC_of_ground {e : Lean.Expr} (hr : Expr.RangeOk e) (hf : e.hasFVar = false)
    (hm : e.hasMVar = false) : okC e = true := by
  rw [Expr.hasFVar_eq hr] at hf
  rw [hasMVar_eq hr, Bool.or_eq_false_iff] at hm
  exact okC_of_flags hr hf hm.1 hm.2

theorem toRules_of_okC : ∀ {rs : List Lean.RecursorRule}, (∀ r ∈ rs, okC r.rhs = true) →
    toRules rs = some (rs.map trRule)
  | [], _ => rfl
  | r :: rs, h => by
    have h1 := toExprC_of_okC (h r (by simp))
    have h2 := toRules_of_okC (rs := rs) fun r' hr' => h r' (by simp [hr'])
    simp [toRules, toRule, h1, h2, trRule]

/-- **A list of block constants in range, without free variables and
metavariables, reads as a record.** -/
theorem toBlock_of_ground : ∀ {l : List Lean.ConstantInfo},
    (∀ ci ∈ l, InLean.isBlockConst ci = true ∧ CIRange ci ∧ CIGround ci) →
    ∃ cb, toBlock l = some cb
  | [], _ => ⟨[], rfl⟩
  | ci :: l, h => by
    obtain ⟨cb, hcb⟩ := toBlock_of_ground (l := l) fun c hc => h c (by simp [hc])
    obtain ⟨hb, hr, hg⟩ := h ci (by simp)
    have hrec : ∃ c, toBlockRecord ci = some c := by
      cases ci with
      | inductInfo v =>
        have : toExprC v.type = some (trC v.type) := toExprC_of_okC (okC_of_ground hr hg.1 hg.2)
        exact ⟨_, by simp only [toBlockRecord, toCV, this]; rfl⟩
      | ctorInfo v =>
        have : toExprC v.type = some (trC v.type) := toExprC_of_okC (okC_of_ground hr hg.1 hg.2)
        exact ⟨_, by simp only [toBlockRecord, toCV, this]; rfl⟩
      | recInfo v =>
        have h1 := toExprC_of_okC (okC_of_ground hr.1 hg.1.1 hg.1.2)
        have h2 := toRules_of_okC (rs := v.rules) fun r hr' =>
          okC_of_ground (hr.2 r hr') (hg.2 r hr').1 (hg.2 r hr').2
        exact ⟨_, by simp only [toBlockRecord, toCV, h1, h2]; rfl⟩
      | _ => simp [InLean.isBlockConst] at hb
    obtain ⟨c, hc⟩ := hrec
    exact ⟨c :: cb, by simp [toBlock, hc, hcb]⟩

theorem mem_of_storedBlock {consts : Array Lean.ConstantInfo} {ci : Lean.ConstantInfo}
    (h : ci ∈ InLean.storedBlock consts) : ci ∈ consts.toList := by
  unfold InLean.storedBlock at h
  simp only [Array.toList_append, List.mem_append, Array.mem_toList_iff, Array.mem_filter] at h
  rw [Array.mem_toList_iff]
  rcases h with (h | h) | h <;> exact h.1

/-- **An inductive block's step.** -/
theorem ind_step {V : Type w} [ConLeche.SetTheory V] (hlaws : EnvLaws)
    {E : Kernel.Environment} {L : ConLeche.Env} {lps : List Name} {nP : Nat}
    {types : List InductiveType} {a : InLean.Added}
    (ha : InLean.checkDecl (theoremConfig lim) E (.inductDecl lps nP types false) = .ok a)
    (hR : EnvRel E L) (hM : ConLeche.Model.EnvModelOk V L) :
    ∃ L', EnvRel (a.consts.foldl InLean.addConst E) L' ∧
      ConLeche.Model.EnvModelOk V L' ∧ ∃ new, L'.consts = new ++ L.consts := by
  obtain ⟨s', hK, hbn, hsq⟩ := checkDecl_run ha
  have hK' : (InLean.checkInductiveC .verified { env := E, coreAxioms := false, limits := lim } lps nP types
      false).run {} = .ok (a, s') := hK
  have hok := checkInductiveC_ok hK'
  have hnd : (a.consts.toList.map (·.name)).Nodup :=
    List.Pairwise.of_map toName (R := (· ≠ ·)) (fun _ _ h e => h (by rw [e]))
      ((namesNodup_iff _).1 hok.2.2.2.2.2.2.2.1)
  have hrun := hok.2.2.2.2.2.2.2.2.2 rfl
  have hJ := jobEnvI_of (lim := lim) hlaws hR hM
  have hsub := storedBlock_of_checkInductiveC hK'
  have hfresh := fresh_of_checkInductiveC hK'
  have hblk : ∀ ci ∈ a.consts.toList, InLean.isBlockConst ci = true := by
    intro ci hci
    have h1 := hok.1
    rw [Array.all_eq_true_iff_forall_mem] at h1
    exact h1 ci (Array.mem_toList_iff.1 hci)
  have hCIR : ∀ ci ∈ a.consts.toList, CIRange ci := by
    intro ci hci
    have h2 := hok.2.1
    rw [Array.all_eq_true_iff_forall_mem] at h2
    exact CIRange_of_constInRange (h2 ci (Array.mem_toList_iff.1 hci))
  obtain ⟨cb, hcb⟩ := toBlock_of_ground (l := InLean.storedBlock a.consts) fun ci hci =>
    ⟨hblk ci (mem_of_storedBlock hci), hCIR ci (mem_of_storedBlock hci),
      CIGround_of_constGround (by
        have h9 := hok.2.2.2.2.2.2.2.2.1
        rw [Array.all_eq_true_iff_forall_mem] at h9
        exact h9 ci (Array.mem_toList_iff.1 (mem_of_storedBlock hci)))⟩
  have hnsorry : ∀ ci ∈ a.consts.toList, ci.name ≠ InLean.sorryAxName := by
    intro ci hci hn
    have h1 := hsq ci hci
    have h2 := hblk ci hci
    cases ci <;> simp_all [InLean.sorryAxSquat, InLean.isBlockConst]
  -- master's step on the block's record
  obtain ⟨-, F, L₁, hkind⟩ := checkIndDeclC_sim (pins := loadedPins) hJ
    (fun ci hci hn => absurd hn (hnsorry ci (mem_of_storedBlock hci))) CSOKIF_empty
    (fun ci hci => hCIR ci (mem_of_storedBlock hci))
    (fun ci hci => closed_of_checkInductiveC hK' ci (mem_of_storedBlock hci))
    (blockStepsOk_storedBlock hok.2.2.2.2.2.2.1) hcb hrun
  obtain ⟨v, rest, hhead⟩ := checkIndDeclC_head hrun
  have hnP := numParams_of_checkIndDeclC hrun hhead
  have hd : toDecl (InLean.storedBlock a.consts) = some (.indDecl cb nP) := by
    rw [hhead] at hcb ⊢
    simp only [toDecl, hcb, hnP, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  have hstep := checkDecl_of_kind hkind
    (basisNamesOk_ind_tr (n := nP) hcb (fun ci hci => hCIR ci (mem_of_storedBlock hci)) hbn)
  have hfold : [ConLeche.Declaration.indDecl cb nP].foldlM
      (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) loadedPins) L = .ok L₁ := by
    simp [List.foldlM, hstep, bind, Except.bind, pure, Except.pure]
  have hpres := indGroupPresBP hlaws _ L a.consts nP {} s' _ hR.presL rfl hsub hfresh hnd
    (sees_of_checkInductiveC hK' hnsorry) hok.2.1 hok.2.2.2.2.2.2.1 hrun hd
  have hproj := projBodiesInRange_ind hlaws hR.projL (ctorsStored_of_pres hR.presL) hK' hfresh hnd
  refine step_of hM hfold ?_
  rw [foldlM_checkDecl_env _ L hfold]
  exact ⟨presI_congr hpres rfl rfl rfl (fun _ => rfl),
    projBodiesInRange_of_findProj (fun _ _ => rfl) hproj⟩

/-! ## The theorem -/

/-- The conclusion at two environments storing alike. -/
theorem concl_congr {V : Type w} [ConLeche.SetTheory V] {E₁ E₂ : Kernel.Environment}
    {L : ConLeche.Env} (h : ∀ n, E₂.find? n = E₁.find? n)
    (hc : ∃ L', EnvRel E₁ L' ∧ ConLeche.Model.EnvModelOk V L' ∧
      ∃ new, L'.consts = new ++ L.consts) :
    ∃ L', EnvRel E₂ L' ∧ ConLeche.Model.EnvModelOk V L' ∧
      ∃ new, L'.consts = new ++ L.consts := by
  obtain ⟨L', ⟨hpres, hproj⟩, hM, hnew⟩ := hc
  exact ⟨L',
    ⟨presI_congr hpres rfl rfl rfl (fun n => h n), projBodiesInRange_congr (fun n => h n) hproj⟩,
    hM, hnew⟩

theorem foldl_single (E : Kernel.Environment) (ci : Lean.ConstantInfo) :
    (#[ci] : Array Lean.ConstantInfo).foldl InLean.addConst E = InLean.addConst E ci := by
  rw [← Array.foldl_toList]; rfl

/-- **The simulation theorem**: if the kernel environment `E` is related to a
con-leche environment `L` with a model, and InLean's `addDecl` at con-leche's
axiom policy accepts a safe declaration in range that is not a non-standard
axiom, some extension of `L` with a model is related to the new
environment — under any resource limits (`InLean.Limits`: the recursion
bound, the numerals' size bound, any poll). -/
@[expose] def AddDeclSound (V : Type w) [ConLeche.SetTheory V] : Prop :=
  EnvLaws →
  ∀ (lim : InLean.Limits) (E E' : Kernel.Environment) (d : Declaration) (L : ConLeche.Env),
    SafeDecl d → DeclRangeOk d → EnvRel E L → ConLeche.Model.EnvModelOk V L →
    InLean.addDecl E d (theoremConfig lim) = .ok E' →
    ∃ L', EnvRel E' L' ∧ ConLeche.Model.EnvModelOk V L' ∧
      ∃ new, L'.consts = new ++ L.consts

/-- **The simulation theorem, proved.** -/
theorem addDeclSound (V : Type w) [ConLeche.SetTheory V] :
    AddDeclSound V := by
  intro hlaws lim E E' d L hd hdr hR hM h
  unfold InLean.addDecl at h
  split at h
  case h_2 => cases h
  rename_i a ha
  cases h
  have hq : ∀ (b : Bool) (E₁ : Kernel.Environment) n,
      (if b = true then InLean.markQuot E₁ else E₁).find? n = E₁.find? n := by
    intro b E₁ n; cases b
    · rfl
    · exact markQuot_find hlaws E₁ n
  obtain ⟨s', hK, -, hsq⟩ := checkDecl_run ha
  have hns : ∀ ci, (∀ v, ci ≠ .axiomInfo v) → ci ∈ a.consts.toList →
      ci.name = InLean.sorryAxName → False := by
    intro ci hax hci hn
    have := hsq ci hci
    cases ci <;> simp_all [InLean.sorryAxSquat, Lean.ConstantInfo.name,
      Lean.ConstantInfo.toConstantVal]
  cases d with
  | axiomDecl v =>
    obtain ⟨rfl, hfresh⟩ := axiom_shape (fe := { env := E, coreAxioms := false, limits := lim }) hK
    refine concl_congr (fun n => by rw [hq, foldl_single]) ?_
    refine single_step hlaws hd hdr (fun _ _ _ _ h => by cases h) ha rfl hfresh
      (fun _ h => by cases h) hR hM fun d' hd' => ?_
    by_cases hqs : v.name = InLean.quotSoundName
    · exact presI_quotSound hlaws hR.pres hd' hfresh hdr hd.1
        (checkAxiomC_quotSound (fe := { env := E, coreAxioms := false, limits := lim }) hK hqs).2.1
    · exact presI_axiom hlaws hR.pres hd' hfresh hdr hqs hd.1 fun _ => rfl
  | defnDecl v =>
    obtain ⟨rfl, hfresh⟩ := defn_shape (fe := { env := E, coreAxioms := false, limits := lim }) hd hK
    refine concl_congr (fun n => by rw [hq, foldl_single]) ?_
    exact single_step hlaws hd hdr (fun _ _ _ _ h => by cases h) ha rfl hfresh
      (fun _ h => by cases h) hR hM fun d' hd' =>
        presI_defn hlaws hR.pres hd' hfresh hdr.1 hdr.2 hd fun hn =>
          (hns (.defnInfo v) (fun _ h => by cases h) (by simp) hn).elim
  | thmDecl v =>
    obtain ⟨rfl, hfresh⟩ := thm_shape (fe := { env := E, coreAxioms := false, limits := lim }) hK
    refine concl_congr (fun n => by rw [hq, foldl_single]) ?_
    exact single_step hlaws hd hdr (fun _ _ _ _ h => by cases h) ha rfl hfresh
      (fun _ h => by cases h) hR hM fun d' hd' =>
        presI_thm hlaws hR.pres hd' hfresh hdr.1 fun hn =>
          (hns (.thmInfo v) (fun _ h => by cases h) (by simp) hn).elim
  | opaqueDecl v =>
    obtain ⟨rfl, hfresh⟩ := opaque_shape (fe := { env := E, coreAxioms := false, limits := lim }) hK
    refine concl_congr (fun n => by rw [hq, foldl_single]) ?_
    exact single_step hlaws hd hdr (fun _ _ _ _ h => by cases h) ha rfl hfresh
      (fun _ h => by cases h) hR hM fun d' hd' =>
        presI_opaque hlaws hR.pres hd' hfresh hdr.1 hd fun hn =>
          (hns (.opaqueInfo v) (fun _ h => by cases h) (by simp) hn).elim
  | mutualDefnDecl vs => exact hd.elim
  | quotDecl =>
    obtain ⟨hqt, hc⟩ := quot_step hlaws ha hR hM
    simp only [hqt, ↓reduceIte]
    exact hc
  | inductDecl lps nP types u =>
    have hu : u = false := hd
    subst hu
    exact concl_congr (fun n => hq _ _ n) (ind_step hlaws ha hR hM)

/-- **No proof of `False`**: under the target, InLean never adds a safe
constant whose type reads as `False` to an environment related to one with a
model (`sorryAx` aside: con-leche's policy hides it, so nothing it checks can
use it). -/
theorem no_false_of_addDeclSound (V : Type w) [ConLeche.SetTheory V] (hS : AddDeclSound V)
    (hlaws : EnvLaws) {E E' : Kernel.Environment} {d : Declaration} {L : ConLeche.Env}
    (hd : SafeDecl d) (hdr : DeclRangeOk d) (hR : EnvRel E L)
    (hM : ConLeche.Model.EnvModelOk V L)
    (h : InLean.addDecl E d (theoremConfig lim) = .ok E')
    {n : Name} {ci : Lean.ConstantInfo} (hci : E'.find? n = some ci) (hsafe : SafeConst ci)
    (hn : n ≠ InLean.sorryAxName)
    (hfalse : toExprC ci.type = some (.const ConLeche.falseName [])) : False := by
  obtain ⟨L', hR', hM', -⟩ := hS hlaws lim E E' d L hd hdr hR hM h
  obtain ⟨c, hc, -, hty⟩ := hR'.reads hci hsafe hn
  obtain ⟨mp⟩ := hM'.nonempty
  rw [hfalse] at hty
  exact ConLeche.Model.no_constant_of_False mp c hc (Option.some.inj hty).symm

/-- **No proof of `False`**: InLean never adds a safe constant whose type reads
as `False` to an environment related to one with a model (`sorryAx` aside). -/
theorem no_false (V : Type w) [ConLeche.SetTheory V]
    (hlaws : EnvLaws) {E E' : Kernel.Environment} {d : Declaration} {L : ConLeche.Env}
    (hd : SafeDecl d) (hdr : DeclRangeOk d) (hR : EnvRel E L)
    (hM : ConLeche.Model.EnvModelOk V L)
    (h : InLean.addDecl E d (theoremConfig lim) = .ok E')
    {n : Name} {ci : Lean.ConstantInfo} (hci : E'.find? n = some ci) (hsafe : SafeConst ci)
    (hn : n ≠ InLean.sorryAxName)
    (hfalse : toExprC ci.type = some (.const ConLeche.falseName [])) : False :=
  no_false_of_addDeclSound V (addDeclSound V) hlaws hd hdr hR hM h hci hsafe hn hfalse

end InLeanProof
