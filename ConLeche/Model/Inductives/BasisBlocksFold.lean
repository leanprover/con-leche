module

public import ConLeche.Model.Inductives.EnvModelBStages
public import ConLeche.Model.Inductives.BasisBlocksStep
public import ConLeche.Model.Inductives.BasisBlocksUnit
public import ConLeche.Model.Inductives.BasisBlocksNat
public import ConLeche.Model.Inductives.BasisBlocksEq
import ConLeche.Model.Fold
public section

/-!
# The basis step at the model WITH ITS BLOCKS (task #315, M7-3 session 9)

§U.45 (e) left the basis tier of the flip with one gap: the pinned
blocks all carry their block models (`BasisBlocks*.lean`) and the step's
shape is stated (`EnvBlocksOf.extendBasisOf`), but `declBasisPB_*`
handed back an ANONYMOUS model, so the run's crossing facts could not
be stated about it.  Session 9 closed that (`basisStepAgree_of`,
`Model/Fold.lean`), and this module is what it unlocks: the five
instantiations, and the basis step at `EnvModelB`.

The crossing inputs come from ONE record per block — `BlockInstallExt`
(`EnvModelBStages.lean`), the same one the mutual and native routes
use.  A pinned block tables nothing, so the readings cross on the
carriers' agreement alone (`denoteMeta_env_mono`, no guard), which is
why the basis tier needs no `ProjFree` bookkeeping.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule ContainerInfo ContainerMember
  IndCaps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## The step, off one install record -/

/-- **THE BASIS STEP, off one install record** (task #315 M7-3 session
9, DESIGN §U.61 (b)): `EnvBlocksOf.extendBasisOf`'s ten lookup and
reading premises, all read off `BlockInstallExt` at a block that tables
nothing, plus the carriers' agreement the run now hands back. -/
theorem EnvBlocksOf.extendBasisExt {env₁ env₂ : Env} {m₁ : EnvModel V env₁} {m₂ : EnvModel V env₂}
    {Ms : List Name} {new : List ConstantInfo} {B : ContainerInfo → BlockModel V}
    {ci₀ : ContainerInfo} {d₀ : BlockModel V} {J₀ : Name}
    (hI : BlockInstallExt Ms env₁ env₂ new)
    (hMs : ∀ n ∈ Ms, n ∈ new.map (·.name))
    (hnoTbl : ∀ c ∈ new, ∀ tbl : ConLeche.ProjTable, c ≠ .projInfo tbl)
    (hag : AcvalAgrees m₁ m₂)
    (hfreshM : ∃ M ∈ ci₀.members, env₁.find? M.name = none)
    (hb : EnvBlocksOf m₁ B)
    (hread : ConLeche.containerInfo? env₂ J₀ = some ci₀)
    (hother : ∀ J ∈ new.map (·.name), J ≠ J₀ →
      ∃ c : ConstantInfo, env₂.find? J = some c ∧ ∀ cv caps, c ≠ .indInfo cv caps)
    (hAt : BlockAt m₂ (extendAt B ci₀ d₀) ci₀) :
    EnvBlocksOf m₂ (extendAt B ci₀ d₀) := by
  have hF : FindPreserved env₁ env₂ := fun hf => hI.ext _ _ hf
  refine EnvBlocksOf.extendBasisOf hI.ext hI.newN hI.freshN (hI.recN hMs) m₁.wf m₁.rec_ctors
    (fun n c _ hf => hI.ext n c hf) (constsResolve_of_findPreserved hF) hag
    (fun ψ dp e ea hr => ?_) hfreshM hb hread hother hAt
  rw [denoteMeta_acval_congr (fun n hn => (hag n hn).symm) dp e] at hr
  exact denoteMeta_env_mono hF (litGuardsMono_of_findPreserved hF)
    (hI.toConsExt.noNewTables hnoTbl) dp e hr

/-! ## The five blocks -/

omit [SetTheory V] in
/-- A name the extension does not answer is not the base's either. -/
theorem find?_none_of_ext {env env' : Env} (hF : FindPreserved env env') {n : Name}
    (h : env'.find? n = none) : env.find? n = none := by
  cases hf : env.find? n with
  | none => rfl
  | some c => rw [hF hf] at h; exact nomatch h

/-- **`Empty`'s block survives its own install** (task #315 M7-3
session 9): `extendBasisExt` at the two-cons block, with the read-back
computed (`containerInfo?_emptyA`) and the group's obligation the
block's own (`emptyBlockAt`). -/
theorem emptyBlocksStepOf {env env₂ : Env} {m₁ : EnvModel V env} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V}
    (h : ConLeche.Semantics.BasisInstallRun env ConLeche.BasisKind.emptyK.declsA env₂)
    (hag : AcvalAgrees m₁ m₂) (hb : EnvBlocksOf m₁ B) :
    EnvBlocksOf m₂ (extendAt B
      ⟨0, [⟨ConLeche.emptyName, [], ConLeche.emptyA.toConstantVal.type, []⟩]⟩
      (zeroCtorBlock (V := V) ConLeche.emptyName (.succ .zero) ⟨[]⟩)) := by
  rw [show ConLeche.BasisKind.emptyK.declsA = [emptyA, emptyRecA] from rfl] at h
  obtain ⟨h1, h2, hnil⟩ := h
  subst hnil
  have hf1 : env.find? emptyA.name = none := Option.isNone_iff_eq_none.mp h1
  have hf2 : env.find? emptyRecA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) (Option.isNone_iff_eq_none.mp h2)
  have hI : BlockInstallExt [ConLeche.emptyName] env
      ⟨emptyRecA :: emptyA :: env.consts⟩ [emptyRecA, emptyA] := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hf2
      · rcases List.mem_singleton.mp hc' with rfl
        exact hf1
    · intro c hc cv caps heq
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc' with rfl
        exact List.mem_singleton.mpr rfl
    · intro c hc cv mI rP rules heq
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact ⟨ConLeche.emptyName, List.mem_singleton.mpr rfl, rfl⟩
      · rcases List.mem_singleton.mp hc' with rfl
        exact nomatch heq
    · intro c hc tbl heq
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc' with rfl
        exact nomatch heq
  have hT : (⟨emptyRecA :: emptyA :: env.consts⟩ : Env).find? ConLeche.emptyName
      = some emptyA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hR : (⟨emptyRecA :: emptyA :: env.consts⟩ : Env).find?
      (ConLeche.emptyName.str "rec") = some emptyRecA := by
    rw [ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hMs : ∀ n ∈ [ConLeche.emptyName], n ∈ ([emptyRecA, emptyA].map (·.name)) := by
    intro n hn
    simp only [List.mem_singleton] at hn
    subst hn
    exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  have hnoTbl : ∀ c ∈ [emptyRecA, emptyA], ∀ tbl : ConLeche.ProjTable,
      c ≠ .projInfo tbl := by
    intro c hc tbl
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact fun heq => nomatch heq
    · obtain rfl : c = emptyA := List.mem_singleton.mp hc'
      exact fun heq => nomatch heq
  have hother : ∀ J ∈ ([emptyRecA, emptyA].map (·.name)), J ≠ ConLeche.emptyName →
      ∃ c : ConstantInfo, (⟨emptyRecA :: emptyA :: env.consts⟩ : Env).find? J = some c ∧
        ∀ cv caps, c ≠ .indInfo cv caps := by
    intro J hJ hne
    rcases List.mem_cons.mp hJ with rfl | hJ'
    · exact ⟨emptyRecA, hR, fun _ _ heq => nomatch heq⟩
    · obtain rfl : J = emptyA.name := List.mem_singleton.mp hJ'
      exact absurd rfl hne
  exact EnvBlocksOf.extendBasisExt (J₀ := ConLeche.emptyName) hI hMs hnoTbl hag
    ⟨_, List.mem_singleton.mpr rfl, hf1⟩ hb (containerInfo?_emptyA hT hR) hother
    (emptyBlockAt hT (extendAt_self _ _ _))

/-- **`False`'s block survives its own install** (task #315 M7-3
session 9): `emptyBlocksStepOf` one universe down — the same
two-cons block, the same zero-constructor block model at grade
`.zero` (`containerInfo?_falseA`, `falseBlockAt`). -/
theorem falseBlocksStepOf {env env₂ : Env} {m₁ : EnvModel V env} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V}
    (h : ConLeche.Semantics.BasisInstallRun env ConLeche.BasisKind.falseK.declsA env₂)
    (hag : AcvalAgrees m₁ m₂) (hb : EnvBlocksOf m₁ B) :
    EnvBlocksOf m₂ (extendAt B
      ⟨0, [⟨ConLeche.falseName, [], ConLeche.falseA.toConstantVal.type, []⟩]⟩
      (zeroCtorBlock (V := V) ConLeche.falseName .zero ⟨[]⟩)) := by
  rw [show ConLeche.BasisKind.falseK.declsA = [falseA, falseRecA] from rfl] at h
  obtain ⟨h1, h2, hnil⟩ := h
  subst hnil
  have hf1 : env.find? falseA.name = none := Option.isNone_iff_eq_none.mp h1
  have hf2 : env.find? falseRecA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) (Option.isNone_iff_eq_none.mp h2)
  have hI : BlockInstallExt [ConLeche.falseName] env
      ⟨falseRecA :: falseA :: env.consts⟩ [falseRecA, falseA] := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hf2
      · rcases List.mem_singleton.mp hc' with rfl
        exact hf1
    · intro c hc cv caps heq
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc' with rfl
        exact List.mem_singleton.mpr rfl
    · intro c hc cv mI rP rules heq
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact ⟨ConLeche.falseName, List.mem_singleton.mpr rfl, rfl⟩
      · rcases List.mem_singleton.mp hc' with rfl
        exact nomatch heq
    · intro c hc tbl heq
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc' with rfl
        exact nomatch heq
  have hT : (⟨falseRecA :: falseA :: env.consts⟩ : Env).find? ConLeche.falseName
      = some falseA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hR : (⟨falseRecA :: falseA :: env.consts⟩ : Env).find?
      (ConLeche.falseName.str "rec") = some falseRecA := by
    rw [ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hMs : ∀ n ∈ [ConLeche.falseName], n ∈ ([falseRecA, falseA].map (·.name)) := by
    intro n hn
    simp only [List.mem_singleton] at hn
    subst hn
    exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  have hnoTbl : ∀ c ∈ [falseRecA, falseA], ∀ tbl : ConLeche.ProjTable,
      c ≠ .projInfo tbl := by
    intro c hc tbl
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact fun heq => nomatch heq
    · obtain rfl : c = falseA := List.mem_singleton.mp hc'
      exact fun heq => nomatch heq
  have hother : ∀ J ∈ ([falseRecA, falseA].map (·.name)), J ≠ ConLeche.falseName →
      ∃ c : ConstantInfo, (⟨falseRecA :: falseA :: env.consts⟩ : Env).find? J = some c ∧
        ∀ cv caps, c ≠ .indInfo cv caps := by
    intro J hJ hne
    rcases List.mem_cons.mp hJ with rfl | hJ'
    · exact ⟨falseRecA, hR, fun _ _ heq => nomatch heq⟩
    · obtain rfl : J = falseA.name := List.mem_singleton.mp hJ'
      exact absurd rfl hne
  exact EnvBlocksOf.extendBasisExt (J₀ := ConLeche.falseName) hI hMs hnoTbl hag
    ⟨_, List.mem_singleton.mpr rfl, hf1⟩ hb (containerInfo?_falseA hT hR) hother
    (falseBlockAt hT (extendAt_self _ _ _))

/-- **`PUnit`'s block survives its own install** (task #315 M7-3
session 9): the three-cons block (former, constructor, recursor), with
the read-back computed (`containerInfo?_punitA`) and the group's
obligation the block's own (`punitBlockAt`). -/
theorem punitBlocksStepOf {env env₂ : Env} {m₁ : EnvModel V env} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V}
    (h : ConLeche.Semantics.BasisInstallRun env ConLeche.BasisKind.punitK.declsA env₂)
    (hag : AcvalAgrees m₁ m₂) (hb : EnvBlocksOf m₁ B) :
    EnvBlocksOf m₂ (extendAt B
      ⟨0, [⟨ConLeche.punitName, [ConLeche.uN], ConLeche.punitA.toConstantVal.type,
        [⟨ConLeche.punitUnitName, ConLeche.punitUnitA.toConstantVal.type, 0⟩]⟩]⟩
      (punitBlock (V := V))) := by
  rw [show ConLeche.BasisKind.punitK.declsA = [punitA, punitUnitA, punitRecA] from rfl] at h
  obtain ⟨h1, h2, h3, hnil⟩ := h
  subst hnil
  have hf1 : env.find? punitA.name = none := Option.isNone_iff_eq_none.mp h1
  have h2' : (⟨punitA :: env.consts⟩ : Env).find? punitUnitA.name = none :=
    Option.isNone_iff_eq_none.mp h2
  have h3' : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find? punitRecA.name = none :=
    Option.isNone_iff_eq_none.mp h3
  have hf2 : env.find? punitUnitA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) h2'
  have hf3 : env.find? punitRecA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) (find?_none_of_ext (findPreserved_cons h2') h3')
  have hI : BlockInstallExt [ConLeche.punitName] env
      ⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ [punitRecA, punitUnitA, punitA] := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact hf3
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact hf2
      · rcases List.mem_singleton.mp hc2 with rfl
        exact hf1
    · intro c hc cv caps heq
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact nomatch heq
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc2 with rfl
        exact List.mem_singleton.mpr rfl
    · intro c hc cv mI rP rules heq
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact ⟨ConLeche.punitName, List.mem_singleton.mpr rfl, rfl⟩
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc2 with rfl
        exact nomatch heq
    · intro c hc tbl heq
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact nomatch heq
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc2 with rfl
        exact nomatch heq
  have hT : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env).find? ConLeche.punitName
      = some punitA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons,
      if_neg (by decide), ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hU : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env).find?
      ConLeche.punitUnitName = some punitUnitA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hR : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env).find?
      ConLeche.punitRecName = some punitRecA := by
    rw [ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hMs : ∀ n ∈ [ConLeche.punitName],
      n ∈ ([punitRecA, punitUnitA, punitA].map (·.name)) := by
    intro n hn
    simp only [List.mem_singleton] at hn
    subst hn
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
  have hnoTbl : ∀ c ∈ [punitRecA, punitUnitA, punitA], ∀ tbl : ConLeche.ProjTable,
      c ≠ .projInfo tbl := by
    intro c hc tbl
    rcases List.mem_cons.mp hc with rfl | hc1
    · exact fun heq => nomatch heq
    rcases List.mem_cons.mp hc1 with rfl | hc2
    · exact fun heq => nomatch heq
    · obtain rfl : c = punitA := List.mem_singleton.mp hc2
      exact fun heq => nomatch heq
  have hother : ∀ J ∈ ([punitRecA, punitUnitA, punitA].map (·.name)), J ≠ ConLeche.punitName →
      ∃ c : ConstantInfo,
        (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env).find? J = some c ∧
        ∀ cv caps, c ≠ .indInfo cv caps := by
    intro J hJ hne
    rcases List.mem_cons.mp hJ with rfl | hJ1
    · exact ⟨punitRecA, hR, fun _ _ heq => nomatch heq⟩
    rcases List.mem_cons.mp hJ1 with rfl | hJ2
    · exact ⟨punitUnitA, hU, fun _ _ heq => nomatch heq⟩
    · obtain rfl : J = punitA.name := List.mem_singleton.mp hJ2
      exact absurd rfl hne
  exact EnvBlocksOf.extendBasisExt (J₀ := ConLeche.punitName) hI hMs hnoTbl hag
    ⟨_, List.mem_singleton.mpr rfl, hf1⟩ hb (containerInfo?_punitA hT hR hU) hother
    (punitBlockAt hT hU (extendAt_self _ _ _))

/-- **`Nat`'s block survives its own install** (task #315 M7-3 session
9): the four-cons block (former, the two constructors, recursor), with
the read-back computed (`containerInfo?_natA`) and the group's
obligation the block's own (`natBlockAt`). -/
theorem natBlocksStepOf {env env₂ : Env} {m₁ : EnvModel V env} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V}
    (h : ConLeche.Semantics.BasisInstallRun env ConLeche.BasisKind.natK.declsA env₂)
    (hag : AcvalAgrees m₁ m₂) (hb : EnvBlocksOf m₁ B) :
    EnvBlocksOf m₂ (extendAt B
      ⟨0, [⟨ConLeche.natName, [], ConLeche.natA.toConstantVal.type,
        [⟨ConLeche.natZeroName, ConLeche.natZeroA.toConstantVal.type, 0⟩,
         ⟨ConLeche.natSuccName, ConLeche.natSuccA.toConstantVal.type, 1⟩]⟩]⟩
      (natBlock (V := V))) := by
  rw [show ConLeche.BasisKind.natK.declsA = [natA, natZeroA, natSuccA, natRecA] from rfl] at h
  obtain ⟨h1, h2, h3, h4, hnil⟩ := h
  subst hnil
  have hf1 : env.find? natA.name = none := Option.isNone_iff_eq_none.mp h1
  have h2' : (⟨natA :: env.consts⟩ : Env).find? natZeroA.name = none :=
    Option.isNone_iff_eq_none.mp h2
  have h3' : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natSuccA.name = none :=
    Option.isNone_iff_eq_none.mp h3
  have h4' : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find? natRecA.name = none :=
    Option.isNone_iff_eq_none.mp h4
  have hf2 : env.find? natZeroA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) h2'
  have hf3 : env.find? natSuccA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) (find?_none_of_ext (findPreserved_cons h2') h3')
  have hf4 : env.find? natRecA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) (find?_none_of_ext (findPreserved_cons h2')
      (find?_none_of_ext (findPreserved_cons h3') h4'))
  have hI : BlockInstallExt [ConLeche.natName] env
      ⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩
      [natRecA, natSuccA, natZeroA, natA] := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact hf4
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact hf3
      rcases List.mem_cons.mp hc2 with rfl | hc3
      · exact hf2
      · rcases List.mem_singleton.mp hc3 with rfl
        exact hf1
    · intro c hc cv caps heq
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact nomatch heq
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact nomatch heq
      rcases List.mem_cons.mp hc2 with rfl | hc3
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc3 with rfl
        exact List.mem_singleton.mpr rfl
    · intro c hc cv mI rP rules heq
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact ⟨ConLeche.natName, List.mem_singleton.mpr rfl, rfl⟩
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact nomatch heq
      rcases List.mem_cons.mp hc2 with rfl | hc3
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc3 with rfl
        exact nomatch heq
    · intro c hc tbl heq
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact nomatch heq
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact nomatch heq
      rcases List.mem_cons.mp hc2 with rfl | hc3
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc3 with rfl
        exact nomatch heq
  have hT : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
      ConLeche.natName = some natA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons,
      if_neg (by decide), ConLeche.Env.find?_cons, if_neg (by decide),
      ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hZ : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
      ConLeche.natZeroName = some natZeroA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons,
      if_neg (by decide), ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hS : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
      ConLeche.natSuccName = some natSuccA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hR : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
      (ConLeche.natName.str "rec") = some natRecA := by
    rw [ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hMs : ∀ n ∈ [ConLeche.natName],
      n ∈ ([natRecA, natSuccA, natZeroA, natA].map (·.name)) := by
    intro n hn
    simp only [List.mem_singleton] at hn
    subst hn
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)))
  have hnoTbl : ∀ c ∈ [natRecA, natSuccA, natZeroA, natA], ∀ tbl : ConLeche.ProjTable,
      c ≠ .projInfo tbl := by
    intro c hc tbl
    rcases List.mem_cons.mp hc with rfl | hc1
    · exact fun heq => nomatch heq
    rcases List.mem_cons.mp hc1 with rfl | hc2
    · exact fun heq => nomatch heq
    rcases List.mem_cons.mp hc2 with rfl | hc3
    · exact fun heq => nomatch heq
    · obtain rfl : c = natA := List.mem_singleton.mp hc3
      exact fun heq => nomatch heq
  have hother : ∀ J ∈ ([natRecA, natSuccA, natZeroA, natA].map (·.name)),
      J ≠ ConLeche.natName → ∃ c : ConstantInfo,
        (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find? J = some c ∧
        ∀ cv caps, c ≠ .indInfo cv caps := by
    intro J hJ hne
    rcases List.mem_cons.mp hJ with rfl | hJ1
    · exact ⟨natRecA, hR, fun _ _ heq => nomatch heq⟩
    rcases List.mem_cons.mp hJ1 with rfl | hJ2
    · exact ⟨natSuccA, hS, fun _ _ heq => nomatch heq⟩
    rcases List.mem_cons.mp hJ2 with rfl | hJ3
    · exact ⟨natZeroA, hZ, fun _ _ heq => nomatch heq⟩
    · obtain rfl : J = natA.name := List.mem_singleton.mp hJ3
      exact absurd rfl hne
  exact EnvBlocksOf.extendBasisExt (J₀ := ConLeche.natName) hI hMs hnoTbl hag
    ⟨_, List.mem_singleton.mpr rfl, hf1⟩ hb (containerInfo?_natA hT hR hZ hS) hother
    (natBlockAt hT hZ hS (extendAt_self _ _ _))

/-- **`Eq`'s block survives its own install** (task #315 M7-3 session
9): the three-cons block at the two-parameter group, with the
read-back computed (`containerInfo?_eqA`) and the group's obligation
the block's own (`eqBlockAt`).  `Eq` is the one pinned block whose
`BlockAt` reads the P-tier model rather than its carrier alone (the
former's and the constructor's TYPES are read through `mem_type`), so
the step is stated at an `EnvModelM`. -/
theorem eqBlocksStepOf {env env₂ : Env} {m₁ : EnvModel V env} (mp₂ : EnvModelM V μ env₂)
    {B : ContainerInfo → BlockModel V}
    (h : ConLeche.Semantics.BasisInstallRun env ConLeche.BasisKind.eqK.declsA env₂)
    (hag : AcvalAgrees m₁ mp₂.base2) (hb : EnvBlocksOf m₁ B) :
    EnvBlocksOf mp₂.base2 (extendAt B
      ⟨2, [⟨ConLeche.eqName, [ConLeche.uN], ConLeche.eqA.toConstantVal.type,
        [⟨ConLeche.eqReflName, ConLeche.eqReflA.toConstantVal.type, 0⟩]⟩]⟩
      (eqBlock (V := V))) := by
  rw [show ConLeche.BasisKind.eqK.declsA = [eqA, eqReflA, eqRecA] from rfl] at h
  obtain ⟨h1, h2, h3, hnil⟩ := h
  subst hnil
  have hf1 : env.find? eqA.name = none := Option.isNone_iff_eq_none.mp h1
  have h2' : (⟨eqA :: env.consts⟩ : Env).find? eqReflA.name = none :=
    Option.isNone_iff_eq_none.mp h2
  have h3' : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqRecA.name = none :=
    Option.isNone_iff_eq_none.mp h3
  have hf2 : env.find? eqReflA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) h2'
  have hf3 : env.find? eqRecA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) (find?_none_of_ext (findPreserved_cons h2') h3')
  have hI : BlockInstallExt [ConLeche.eqName] env
      ⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ [eqRecA, eqReflA, eqA] := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact hf3
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact hf2
      · rcases List.mem_singleton.mp hc2 with rfl
        exact hf1
    · intro c hc cv caps heq
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact nomatch heq
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc2 with rfl
        exact List.mem_singleton.mpr rfl
    · intro c hc cv mI rP rules heq
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact ⟨ConLeche.eqName, List.mem_singleton.mpr rfl, rfl⟩
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc2 with rfl
        exact nomatch heq
    · intro c hc tbl heq
      rcases List.mem_cons.mp hc with rfl | hc1
      · exact nomatch heq
      rcases List.mem_cons.mp hc1 with rfl | hc2
      · exact nomatch heq
      · rcases List.mem_singleton.mp hc2 with rfl
        exact nomatch heq
  have hT : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find? ConLeche.eqName
      = some eqA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons,
      if_neg (by decide), ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hC : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find? ConLeche.eqReflName
      = some eqReflA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hR : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find?
      (ConLeche.eqName.str "rec") = some eqRecA := by
    rw [ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hMs : ∀ n ∈ [ConLeche.eqName], n ∈ ([eqRecA, eqReflA, eqA].map (·.name)) := by
    intro n hn
    simp only [List.mem_singleton] at hn
    subst hn
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
  have hnoTbl : ∀ c ∈ [eqRecA, eqReflA, eqA], ∀ tbl : ConLeche.ProjTable,
      c ≠ .projInfo tbl := by
    intro c hc tbl
    rcases List.mem_cons.mp hc with rfl | hc1
    · exact fun heq => nomatch heq
    rcases List.mem_cons.mp hc1 with rfl | hc2
    · exact fun heq => nomatch heq
    · obtain rfl : c = eqA := List.mem_singleton.mp hc2
      exact fun heq => nomatch heq
  have hother : ∀ J ∈ ([eqRecA, eqReflA, eqA].map (·.name)), J ≠ ConLeche.eqName →
      ∃ c : ConstantInfo,
        (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find? J = some c ∧
        ∀ cv caps, c ≠ .indInfo cv caps := by
    intro J hJ hne
    rcases List.mem_cons.mp hJ with rfl | hJ1
    · exact ⟨eqRecA, hR, fun _ _ heq => nomatch heq⟩
    rcases List.mem_cons.mp hJ1 with rfl | hJ2
    · exact ⟨eqReflA, hC, fun _ _ heq => nomatch heq⟩
    · obtain rfl : J = eqA.name := List.mem_singleton.mp hJ2
      exact absurd rfl hne
  exact EnvBlocksOf.extendBasisExt (J₀ := ConLeche.eqName) hI hMs hnoTbl hag
    ⟨_, List.mem_singleton.mpr rfl, hf1⟩ hb (containerInfo?_eqA hT hR hC) hother
    (eqBlockAt mp₂ hT hC (extendAt_self _ _ _))

/-- **THE STEP AT A BLOCK THAT CREATES NO GROUP** (task #315 M7-3
session 9): `extendBasisExt` without the new group — the assignment
does not move, because no new name reads a container back.

`Quot`'s block is the pinned instance, and it is also why this one
takes `ConsExt` rather than `BlockInstallExt`: that record asks every
`recInfo` the block conses to be named `I.rec` for a member `I`, and
`Quot.lift` and `Quot.ind` are recursors named otherwise, so no `Ms`
makes it true of the `Quot` install.  `ConsExt` is exactly the lookup
half the crossing reads, and `hrecN` — vacuous at a block none of whose
names is an `_.rec` — replaces what `BlockInstallExt.recN` would have
given. -/
theorem EnvBlocksOf.extendNoGroup {env₁ env₂ : Env} {m₁ : EnvModel V env₁}
    {m₂ : EnvModel V env₂} {new : List ConstantInfo}
    {B : ContainerInfo → BlockModel V}
    (hE : ConsExt env₁ env₂ new)
    (hrecN : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₂.find? (n.str "rec") = some (.recInfo cv mI rP rules) →
      n.str "rec" ∈ new.map (·.name) → n ∈ new.map (·.name))
    (hnoTbl : ∀ c ∈ new, ∀ tbl : ConLeche.ProjTable, c ≠ .projInfo tbl)
    (hag : AcvalAgrees m₁ m₂)
    (hb : EnvBlocksOf m₁ B)
    (hnone : ∀ J ∈ new.map (·.name), ConLeche.containerInfo? env₂ J = none) :
    EnvBlocksOf m₂ B := by
  have hF : FindPreserved env₁ env₂ := fun hf => hE.ext _ _ hf
  refine EnvBlocksOf.crossInd hE.ext hE.newN hE.freshN hrecN m₁.wf m₁.rec_ctors
    (fun n c _ hf => hE.ext n c hf) (constsResolve_of_findPreserved hF) hag
    (fun ψ dp e ea hr => ?_) (fun _ _ _ _ => rfl) hb (fun J hJ ci hci => ?_)
  · rw [denoteMeta_acval_congr (fun n hn => (hag n hn).symm) dp e] at hr
    exact denoteMeta_env_mono hF (litGuardsMono_of_findPreserved hF)
      (hE.noNewTables hnoTbl) dp e hr
  · rw [hnone J hJ] at hci
    exact nomatch hci

/-- **`Quot`'s block survives its own install** (task #315 M7-3
session 9): the five-cons block, and the one basis block that creates
NO container group — `containerInfo?` declines `Quot` outright (it is
official's `quotInfo`, not an inductive), and the block's other four
constants are a constructor, two recursors and an axiom, none of them
a stored inductive.  So the assignment does not move
(`EnvBlocksOf.extendNoGroup`). -/
theorem quotBlocksStepOf {env env₂ : Env} {m₁ : EnvModel V env} {m₂ : EnvModel V env₂}
    {B : ContainerInfo → BlockModel V}
    (h : ConLeche.Semantics.BasisInstallRun env ConLeche.BasisKind.quotK.declsA env₂)
    (hag : AcvalAgrees m₁ m₂) (hb : EnvBlocksOf m₁ B) :
    EnvBlocksOf m₂ B := by
  rw [show ConLeche.BasisKind.quotK.declsA
    = [quotA, quotMkA, quotLiftA, quotIndA, quotSoundA] from rfl] at h
  obtain ⟨h1, h2, h3, h4, h5, hnil⟩ := h
  subst hnil
  have hf1 : env.find? quotA.name = none := Option.isNone_iff_eq_none.mp h1
  have h2' : (⟨quotA :: env.consts⟩ : Env).find? quotMkA.name = none :=
    Option.isNone_iff_eq_none.mp h2
  have h3' : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? quotLiftA.name = none :=
    Option.isNone_iff_eq_none.mp h3
  have h4' : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find? quotIndA.name
      = none := Option.isNone_iff_eq_none.mp h4
  have h5' : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
      quotSoundA.name = none := Option.isNone_iff_eq_none.mp h5
  have hf2 : env.find? quotMkA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) h2'
  have hf3 : env.find? quotLiftA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) (find?_none_of_ext (findPreserved_cons h2') h3')
  have hf4 : env.find? quotIndA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) (find?_none_of_ext (findPreserved_cons h2')
      (find?_none_of_ext (findPreserved_cons h3') h4'))
  have hf5 : env.find? quotSoundA.name = none :=
    find?_none_of_ext (findPreserved_cons hf1) (find?_none_of_ext (findPreserved_cons h2')
      (find?_none_of_ext (findPreserved_cons h3')
        (find?_none_of_ext (findPreserved_cons h4') h5')))
  have hQ : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
      Env).find? ConLeche.quotName = some quotA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons,
      if_neg (by decide), ConLeche.Env.find?_cons, if_neg (by decide),
      ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hM : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
      Env).find? ConLeche.quotMkName = some quotMkA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons,
      if_neg (by decide), ConLeche.Env.find?_cons, if_neg (by decide),
      ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hL : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
      Env).find? ConLeche.quotLiftName = some quotLiftA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons,
      if_neg (by decide), ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hInd : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
      Env).find? ConLeche.quotIndName = some quotIndA := by
    rw [ConLeche.Env.find?_cons, if_neg (by decide), ConLeche.Env.find?_cons]
    exact if_pos rfl
  have hS : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
      Env).find? ConLeche.quotSoundName = some quotSoundA := by
    rw [ConLeche.Env.find?_cons]
    exact if_pos rfl
  refine EnvBlocksOf.extendNoGroup (new := [quotSoundA, quotIndA, quotLiftA, quotMkA, quotA])
    ⟨rfl, ?_⟩ ?_ ?_ hag hb ?_
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc1
    · exact hf5
    rcases List.mem_cons.mp hc1 with rfl | hc2
    · exact hf4
    rcases List.mem_cons.mp hc2 with rfl | hc3
    · exact hf3
    rcases List.mem_cons.mp hc3 with rfl | hc4
    · exact hf2
    · rcases List.mem_singleton.mp hc4 with rfl
      exact hf1
  · intro n cv mI rP rules _ hmem
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hn | hn | hn | hn | hn <;>
      exact absurd (ConLeche.Name.str.inj hn).2 (by decide)
  · intro c hc tbl
    rcases List.mem_cons.mp hc with rfl | hc1
    · exact fun heq => nomatch heq
    rcases List.mem_cons.mp hc1 with rfl | hc2
    · exact fun heq => nomatch heq
    rcases List.mem_cons.mp hc2 with rfl | hc3
    · exact fun heq => nomatch heq
    rcases List.mem_cons.mp hc3 with rfl | hc4
    · exact fun heq => nomatch heq
    · obtain rfl : c = quotA := List.mem_singleton.mp hc4
      exact fun heq => nomatch heq
  · intro J hJ
    rcases List.mem_cons.mp hJ with rfl | hJ1
    · exact containerInfo?_eq_none_of_not_ind hS (fun _ _ heq => nomatch heq)
    rcases List.mem_cons.mp hJ1 with rfl | hJ2
    · exact containerInfo?_eq_none_of_not_ind hInd (fun _ _ heq => nomatch heq)
    rcases List.mem_cons.mp hJ2 with rfl | hJ3
    · exact containerInfo?_eq_none_of_not_ind hL (fun _ _ heq => nomatch heq)
    rcases List.mem_cons.mp hJ3 with rfl | hJ4
    · exact containerInfo?_eq_none_of_not_ind hM (fun _ _ heq => nomatch heq)
    · obtain rfl : J = quotA.name := List.mem_singleton.mp hJ4
      simp [ConLeche.containerInfo?, show quotA.name = ConLeche.quotName from rfl]

/-! ## The basis step at `EnvModelB` -/

/-- **THE BASIS STEP AT `EnvModelB`** (task #315 M7-3 session 9,
DESIGN §U.61 (b)): a pinned basis block carries the fold's invariant
WITH ITS BLOCKS — the model the run hands back is
`basisStepAgree_of`'s, and its blocks are the prefix's assignment
grown by the block's own group (`Quot`'s block grows nothing).

This is the basis tier's half of the M8 flip: every branch is one of
the five instantiations above, and the agreement `basisStepAgree_of`
now returns is exactly what they consume. -/
theorem basisStepB_of {env : Env} (mb : EnvModelB V μ env)
    {kind : ConLeche.BasisKind} {env₂ : Env} (h : DeclBasisRun env kind env₂) :
    Nonempty (EnvModelB V μ env₂) := by
  obtain ⟨B, hb⟩ := mb.blocks
  obtain ⟨mp', hag⟩ := basisStepAgree_of mb.toEnvModelM h
  obtain ⟨-, hchain⟩ := h
  cases kind with
  | eqK => exact ⟨⟨mp', ⟨_, eqBlocksStepOf mp' hchain hag hb⟩⟩⟩
  | natK => exact ⟨⟨mp', ⟨_, natBlocksStepOf hchain hag hb⟩⟩⟩
  | punitK => exact ⟨⟨mp', ⟨_, punitBlocksStepOf hchain hag hb⟩⟩⟩
  | emptyK => exact ⟨⟨mp', ⟨_, emptyBlocksStepOf hchain hag hb⟩⟩⟩
  | falseK => exact ⟨⟨mp', ⟨_, falseBlocksStepOf hchain hag hb⟩⟩⟩
  | quotK => exact ⟨⟨mp', ⟨_, quotBlocksStepOf hchain hag hb⟩⟩⟩
end ConLeche.Model
