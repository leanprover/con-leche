module

public import ConLeche.Model.Inductives.NestedCtorTypedRun
public import ConLeche.Model.Inductives.WhnfContentOfRun
public import ConLeche.Model.Inductives.NestedCtorStage
import ConLeche.Verify.Inductives.NestedCtorNames
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedFacts

public section

/-!
# The restored constructors' model at the run (task #279 M-D′ D3, DESIGN §M.54)

`nestedCtorsModel` (`NestedCtorStage.lean`) builds the model of
`env₂ = consNestedCtors ctorsR.flatten env₁` from the formers' model and,
at every restored constructor, its content `NestedCtorLeaf` — a leaf
and a reading at EVERY level assignment, the leaf depending on the
assignment through the block's level parameters alone.  This module
instantiates it at the run:

* **`nestedCtorLeaf_of_run`** — at one assignment `ψ` and the pins'
  data `cd` it chooses (`pinFacts_of_run`), every restored constructor
  reads (`restoredCtorRead_of_run`) and its leaf at ψ's final table is
  typed (`restoredCtorLeaf_of_run`, the run's core facts from
  `nestedRunCore_of_pinFacts`);
* **`canonLps`** — the assignment restricted to the block's level
  parameters: the leaf and reading at `canonLps p.lps ψ` serve at `ψ`
  (`denoteMeta_params_ext`: the restored type's level parameters are the
  block's), which is `NestedCtorLeaf.params`;
* **`nestedCtorsModel_of_run`** — the model of `env₂` off
  `DeclNestedRun`, under `ContainersRep` (M-E's), the bridge's syntactic
  half at every assignment's pin data (`BridgeSyntax`, ψ's standing
  premise) and the transports' grading at every restored constructor
  (`hvia`, DESIGN §M.54).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType AuxStored NestedPin ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The assignment restricted to the block's level parameters -/

/-- The assignment restricted to the level parameters `lps` (zero
elsewhere). -/
@[expose] def canonLps (lps : List Name) (ψ : Name → Nat) : Name → Nat :=
  fun q => if q ∈ lps then ψ q else 0

omit [SetTheory V] in
theorem canonLps_agree (lps : List Name) (ψ : Name → Nat) : ∀ q ∈ lps, ψ q = canonLps lps ψ q := by
  intro q hq
  unfold canonLps
  rw [if_pos hq]

omit [SetTheory V] in
theorem canonLps_ext {lps : List Name} {ψ₁ ψ₂ : Name → Nat} (h : ∀ q ∈ lps, ψ₁ q = ψ₂ q) :
    canonLps lps ψ₁ = canonLps lps ψ₂ := by
  funext q
  unfold canonLps
  split
  · next hq => exact h q hq
  · rfl

/-! ## The content at one assignment -/

set_option maxHeartbeats 1600000 in
/-- **Every restored constructor's content at one assignment**: at `ψ`
and the pins' data `cd` the run chooses, every `c ∈ ctorsR.flatten` has
a closed, graded, bit-valid leaf, a graded reading of its restored
type at the formers' model, and the leaf a member of the reading —
`restoredCtorRead_of_run` and `restoredCtorLeaf_of_run` at the run's
core facts, under the bridge's syntactic half and the transports'
grading at this assignment. -/
theorem nestedCtorLeaf_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envAux : Env} {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock}
    {params : List Expr} {pbs : List (Expr × ConLeche.BinderMeta)} {stored : List AuxStored}
    {fmsA ctorsA : List ConstantVal} {ctorsR : List (List (ConstantVal × Nat × Nat))}
    {order : List Nat} (mp : EnvModelM V μ env)
    {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hb : ConLeche.auxBlock p st = some b)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st)
    (hord : ConLeche.nestedTopoOrder (ElimState.grp st) p.k st = .ok order)
    (hlenSt : st.types.length = p.k + st.pins.length)
    (hfreshC : ConLeche.copiesFresh env p.k st = true)
    (hcontC : ConLeche.nestedContainersOk env st.pins = true)
    (hparamsLen : params.length = p.nP)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hstoredA : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hpc : ConLeche.pinsClosed p.nP st.pins = true)
    (hK20 : (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true)
    (hK23 : ConLeche.nestedGroupExclusionOk env envAux p st = true)
    (hK17 : ConLeche.nestedCtorsWhnfOk (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
      (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.nP
      (ConLeche.nestedCtorPairs b stored) = .ok ())
    (hpo : PinsAtOpeners st params) (hmo : PinsMentionReal env st params p.k)
    (hhead : ∃ (t₀ : AuxType) (body body₀ : Expr), st.types[0]? = some t₀ ∧
      ConLeche.openPisAtFvars p.nP t₀.type 0 = some (params, body) ∧
      t₀.type.stripPis p.nP = some (pbs, body₀) ∧ pbs.length = p.nP ∧ t₀.type.hasFvar = false)
    (hfreshRec : ∀ t, t < b.k → env.find? (b.recName t) = none)
    (hpinsNP : ∀ q ∈ st.pins, ∀ (T : Name) (i : Nat), env.find? T = none →
      Expr.NoProjAt T i q.pin)
    (hannF : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p.nP
      p.formers = .ok fmsA)
    (hannC : ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA)
    (hctors : (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors) = .ok ctorsR)
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d)
    (hcd : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    (hsyn : BridgeSyntax d st p.k st.pins.length cd (auxOfsOf st p.k cd))
    -- NAMED (DESIGN §M.54): the transports are graded at the leaf frame
    (hvia : ∀ (J : Nat) (cA : ConstantVal × Nat), d.ctorsA[J]? = some cA → d.mems J < p.k →
      ∀ (ρ : Nat → V) (ps fs : List V), ps.length = d.nP → fs.length = cA.2 →
      SpineFit ρ ((d.dsRestored mpAux.base2 ψ p.k J (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
        (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA)).map (·.2.2)) (ps ++ fs) →
      ∀ i, i < cA.2 → d.copyPos p.k J i →
        WellDenotedV V (consList (ps ++ fs) ρ)
          (viaEntryAV (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order (fun _ => .sort 0)
            (d.tgtsR J i - p.k)) cA.2 0 i 0 ((d.tssR J ψ).getD i []) ((d.eissR J ψ).getD i [])))
    (mp₁ : EnvModelM V μ (ConLeche.consNestedFormers (stored.take p.k) env))
    (hF : FindPreserved (ConLeche.consNestedFormers (stored.take p.k) env) envAux)
    (hag₁ : ∀ n : Name, ((ConLeche.consNestedFormers (stored.take p.k) env).find? n).isSome = true →
      mp₁.base2.acval n = mpAux.base2.acval n)
    (hrealStored : ∀ t, t < p.k → ∃ (cv : ConstantVal) (caps : IndCaps),
      (ConLeche.consNestedFormers (stored.take p.k) env).find? (d.memberName t)
        = some (.indInfo cv caps) ∧ cv.levelParams = b.lps) :
    ∀ c ∈ ctorsR.flatten, ∃ A ta : AnnotTerm,
      Term.bvarsBelow 0 A.erase ∧ (∀ ρ : Nat → V, WellDenoted V ρ A) ∧
      (∀ ρ : Nat → V, AnnotValid V ρ A) ∧
      denoteMeta mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env) ψ 0 c.1.type
        = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧ ∀ ρ : Nat → V, interp V ρ A ∈ˢ interp V ρ ta := by
  intro c hc
  -- ## the pins' literal support at the formers' environment (task #311)
  have hup : ∀ n : Name, (env.find? n).isSome = true →
      ((ConLeche.consNestedFormers (stored.take p.k) env).find? n).isSome = true := by
    intro n hn
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hn
    rw [(consNestedFormers_freshExt hK20).find?_some hc']; rfl
  have hfmsLen : fmsA.length = p.k := by
    have h1 := ConLeche.elimNested_length helim
    rw [ConLeche.nestedTypes0_length, hlenSt] at h1
    omega
  have hrepsN := hreps
  obtain ⟨-, -, -, -, -, -, hnames, -⟩ := hrepsN
  have hmono : ∀ n : Name, ((ConLeche.nestedFormerEnv fmsA env).find? n).isSome = true →
      ((ConLeche.consNestedFormers (stored.take p.k) env).find? n).isSome = true := by
    intro n hn
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hn
    rcases ConLeche.nestedFormerEnv_find? hc' with h1 | h1
    · exact hup n h1
    · obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp h1
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hcv
      have htf : t < fmsA.length := (List.getElem?_eq_some_iff.mp ht).1
      have htk : t < p.k := by omega
      have htb : t < b.k := by rw [ConLeche.auxBlock_k hb, hlenSt]; omega
      have hnm := ConLeche.elimNested_name_lt helim (t := t)
        (by rw [ConLeche.nestedTypes0_length]; exact htf)
      rw [ConLeche.nestedTypes0_getElem?, ht] at hnm
      simp only [Option.map_some] at hnm
      obtain ⟨ty, hty, htyn⟩ := Option.map_eq_some_iff.mp hnm
      obtain ⟨cv', caps, hfind, -⟩ := hrealStored t htk
      rw [memberName_eq_type hb hnames hty htb, htyn] at hfind
      rw [hfind]; rfl
  have hpinsLits := pinsLits_of_run mp hmono hannF hannC helim
  -- ## the constructor record, ψ's premise
  have hwalk := copyWalkFacts_of_run hb hlenSt hfreshC hcontC mp.base2.wf hcore hstoredA hpc hK20
    hK17 helim hparamsLen hpo hmo hhead hreps hchk hcd (nestedGroupExclusionOk_inv hK23)
    (fun j'' hj'' => (hcd j'' hj'').1.1.ordNotRec)
  have hwhnfC := whnfContent_of_run hμ hb hlenSt mp.base2.wf hcore (fun t ht => hfreshRec t ht)
    hK20 hparamsLen hmo hhead hpinsNP hreps hcd hwalk hpinsLits mp₁ hF hag₁
    (nestedTbl_fresh_of_run hcore hK20) hrealStored
  have hread : CopyCtorsRead mpAux d ψ st p.k st.pins.length cd := fun j' hj' Jc cAJ hJc =>
    copyCtorAsRead_of_run hb hlenSt hfreshC hcontC hreps hchk hcd hwalk hwhnfC hj' hJc
  obtain ⟨lpsT, R⟩ := nestedRunCore_of_pinFacts hreps hchk hb hlenSt hord hcd hread hsyn
  -- ## the reading and the leaf
  obtain ⟨J, cA, lpsT', hJ, hmemJ, -, -, -, -, hstoredC, hD, hreadC, hokTy⟩ :=
    restoredCtorRead_of_run hμ hb hlenSt hfreshC hcore hstoredA hpc helim hpo hhead hfreshRec hK20
      hmo hpinsNP hreps hchk hcd hpinsLits hctors mp₁ hF hag₁ (nestedTbl_fresh_of_run hcore hK20)
      hrealStored c hc
  obtain ⟨hbelow, hall⟩ := restoredCtorLeaf_of_run R hJ hmemJ hD hstoredC hokTy (fun _ => .sort 0)
    (hvia J cA hJ hmemJ)
  exact ⟨_, _, hbelow, fun ρ => (hall ρ).1, fun ρ => (hall ρ).2.1, hreadC, hokTy,
    fun ρ => (hall ρ).2.2⟩

/-! ## The model of the restored constructors' environment, off the run -/

set_option maxHeartbeats 1600000 in
/-- **The model of `env₂ = consNestedCtors ctorsR.flatten env₁` off
`DeclNestedRun`** (M-D′ D3): `nestedCtorsModel` at the contents of
`nestedCtorLeaf_of_run`, canonicalised to the block's level parameters
(`canonLps`), under `ContainersRep` (M-E's), the bridge's syntactic
half at every assignment's pin data and the transports' grading at
every restored constructor (both NAMED, DESIGN §M.54).  The carrier is
the formers' model's off the constructors' names, which is the
pre-block one's off the block. -/
theorem nestedCtorsModel_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env) (stored : List AuxStored)
      (ctorsR : List (List (ConstantVal × Nat × Nat))) (order : List Nat),
      ConLeche.auxBlock p st = some b ∧
      ConLeche.nestedTopoOrder (ElimState.grp st) p.k st = .ok order ∧
      st.types.length = p.k + st.pins.length ∧
      (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors) = .ok ctorsR ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
        CtorsChecked μ F env b true d ∧ AuxBlockAgree F mp mpAux b true d ∧
        ∃ (params : List Expr) (pbs : List (Expr × ConLeche.BinderMeta)),
          (ContainersRep env envAux mpAux.base2 →
            -- NAMED: the bridge's syntactic half at every assignment's pin data
            (∀ (ψ : Name → Nat) (cd : Nat → CopyData V),
              (∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j) →
              BridgeSyntax d st p.k st.pins.length cd (auxOfsOf st p.k cd)) →
            -- NAMED: the transports are graded at every restored
            -- constructor's leaf frame
            (∀ (ψ : Name → Nat) (cd : Nat → CopyData V),
              (∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j) →
              ∀ (J : Nat) (cA : ConstantVal × Nat), d.ctorsA[J]? = some cA → d.mems J < p.k →
              ∀ (ρ : Nat → V) (ps fs : List V), ps.length = d.nP → fs.length = cA.2 →
              SpineFit ρ ((d.dsRestored mpAux.base2 ψ p.k J
                (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
                (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA)).map (·.2.2)) (ps ++ fs) →
              ∀ i, i < cA.2 → d.copyPos p.k J i →
                WellDenotedV V (consList (ps ++ fs) ρ)
                  (viaEntryAV (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order
                    (fun _ => .sort 0) (d.tgtsR J i - p.k)) cA.2 0 i 0
                    ((d.tssR J ψ).getD i []) ((d.eissR J ψ).getD i []))) →
            ∃ (mp₁ : EnvModelM V μ (ConLeche.consNestedFormers (stored.take p.k) env))
              (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
                (ConLeche.consNestedFormers (stored.take p.k) env))),
              ConLeche.EtaFamiliesClosed (ConLeche.consNestedCtors ctorsR.flatten
                (ConLeche.consNestedFormers (stored.take p.k) env)) ∧
              (∀ n : Name, (env.find? n).isSome = true → mp₁.base2.acval n = mp.base2.acval n) ∧
              (∀ t, t < p.k → mp₁.base2.acval (d.memberName t) = mpAux.base2.acval (d.memberName t)) ∧
              (∀ n : Name, (∀ c ∈ ctorsR.flatten, n ≠ c.1.name) →
                mp₂.base2.acval n = mp₁.base2.acval n)) := by
  obtain ⟨st, b, envAux, params, pbs, fmsA, ctorsA, stored, order, hb, helim, hord, hlenSt, hfreshC,
    hcontC, hparamsLen, hcore, hstoredA, hpc, hK20, hK23, hK17, hpo, hmo, hhead, hfreshRec, hpinsNP,
    hrest, mpAux, d, hreps, hchk, hag, hpins⟩ := pinFacts_of_run hμ mp hE h
  obtain ⟨-, -, hannF, hannC, -, -, ctorsR, _cvRms, _cvRns, _rulesM, _rulesN, hctors, -⟩ := hrest
  refine ⟨st, b, envAux, stored, ctorsR, order, hb, hord, hlenSt, hctors, mpAux, d, hreps, hchk, hag,
    params, pbs, ?_⟩
  intro hcr hsyn hvia
  have hkp : p.k ≤ b.k := by rw [ConLeche.auxBlock_k hb, hlenSt]; omega
  obtain ⟨mp₁, hE₁, hagReal, hagPre, hag₁, hF, hrealStored⟩ := nestedFormersModel mp hE hcore hstoredA
    (fun t ht => (hfreshRec t ht).1) hK20 hkp mpAux d hreps hag
  -- ## the content at every assignment
  have hper : ∀ ψ : Name → Nat, ∀ c ∈ ctorsR.flatten, ∃ A ta : AnnotTerm,
      Term.bvarsBelow 0 A.erase ∧ (∀ ρ : Nat → V, WellDenoted V ρ A) ∧
      (∀ ρ : Nat → V, AnnotValid V ρ A) ∧
      denoteMeta mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env) ψ 0 c.1.type
        = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧ ∀ ρ : Nat → V, interp V ρ A ∈ˢ interp V ρ ta := by
    intro ψ
    obtain ⟨cd, hcd⟩ := hpins hcr ψ
    exact nestedCtorLeaf_of_run hμ mp hb helim hord hlenSt hfreshC hcontC hparamsLen hcore hstoredA
      hpc hK20 hK23 hK17 hpo hmo hhead (fun t ht => (hfreshRec t ht).1) hpinsNP hannF hannC hctors
      hreps hchk hcd (hsyn ψ cd hcd) (hvia ψ cd hcd) mp₁ hF hag₁ hrealStored
  -- ## the restored constructors' front door: the level parameters are the block's
  have hpre : ∀ c ∈ ctorsR.flatten,
      ConLeche.checkConstantValPre (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consNestedFormers (stored.take p.k) env) c.1 = .ok c.1 := by
    intro c hc
    obtain ⟨cs, hcs, hcin⟩ := List.mem_flatten.mp hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcs
    obtain ⟨hlen, hall⟩ := ConLeche.mapM_except_inv hctors
    obtain ⟨a, cs', ha, hcs', hrun⟩ := hall j (by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega)
    rw [hj] at hcs'
    have hcc : cs = cs' := by simpa using hcs'
    rw [hcc] at hcin
    exact ConLeche.restoreCtors_pre hrun c hcin
  have hlpsC : ∀ c ∈ ctorsR.flatten, c.1.levelParams = p.lps := by
    intro c hc
    obtain ⟨-, -, -, -, -, -, -, -, hlps, -, -⟩ :=
      restoredCtor_pos hb hlenSt hstoredA hctors hreps hchk c hc
    exact hlps
  -- ## the leaves and readings, canonicalised
  let Aof : Nat → (Name → Nat) → AnnotTerm := fun i ψ =>
    if hi : i < ctorsR.flatten.length then
      Classical.choose (hper (canonLps p.lps ψ) _ (List.getElem_mem hi))
    else .sort 0
  let taOf : Nat → (Name → Nat) → AnnotTerm := fun i ψ =>
    if hi : i < ctorsR.flatten.length then
      Classical.choose (Classical.choose_spec (hper (canonLps p.lps ψ) _ (List.getElem_mem hi)))
    else .sort 0
  have hleaf : ∀ (i : Nat) (c : ConstantVal × Nat × Nat), ctorsR.flatten[i]? = some c →
      NestedCtorLeaf mp₁ c.1 (Aof i) (taOf i) := by
    intro i c hc
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
    have hmem : ctorsR.flatten[i] ∈ ctorsR.flatten := List.getElem_mem hi
    have hA : ∀ ψ, Aof i ψ = Classical.choose (hper (canonLps p.lps ψ) _ hmem) := fun ψ => by
      show (if hi : i < ctorsR.flatten.length then _ else _) = _
      rw [dif_pos hi]
    have hta : ∀ ψ, taOf i ψ
        = Classical.choose (Classical.choose_spec (hper (canonLps p.lps ψ) _ hmem)) := fun ψ => by
      show (if hi : i < ctorsR.flatten.length then _ else _) = _
      rw [dif_pos hi]
    have hspec : ∀ ψ, Term.bvarsBelow 0 (Aof i ψ).erase ∧
        (∀ ρ : Nat → V, WellDenoted V ρ (Aof i ψ)) ∧ (∀ ρ : Nat → V, AnnotValid V ρ (Aof i ψ)) ∧
        denoteMeta mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env)
          (canonLps p.lps ψ) 0 ctorsR.flatten[i].1.type = some (taOf i ψ) ∧
        (∀ ρ : Nat → V, WellDenotedV V ρ (taOf i ψ)) ∧
        ∀ ρ : Nat → V, interp V ρ (Aof i ψ) ∈ˢ interp V ρ (taOf i ψ) := fun ψ => by
      rw [hA, hta]
      exact Classical.choose_spec (Classical.choose_spec (hper (canonLps p.lps ψ) _ hmem))
    obtain ⟨-, -, -, -, -, -, hlpR, -, -, -, -⟩ :=
      ConLeche.checkConstantValPre_front (hpre _ hmem)
    rw [hlpsC _ hmem] at hlpR
    refine ⟨fun ψ => (hspec ψ).1, fun ψ₁ ψ₂ hagr => ?_, fun ψ ρ => (hspec ψ).2.1 ρ,
      fun ψ ρ => (hspec ψ).2.2.1 ρ, fun ψ => ?_, fun ψ ρ => (hspec ψ).2.2.2.2.1 ρ,
      fun ψ ρ => (hspec ψ).2.2.2.2.2 ρ⟩
    · rw [hA, hA]
      rw [hlpsC _ hmem] at hagr
      have hc' : canonLps p.lps ψ₁ = canonLps p.lps ψ₂ := canonLps_ext hagr
      simp only [hc']
    · rw [denoteMeta_params_ext mp₁.base2 (canonLps_agree p.lps ψ) 0 _ hlpR]
      exact (hspec ψ).2.2.2.1
  obtain ⟨mp₂, hE₂, hagC, -⟩ := nestedCtorsModel mp₁ hE₁ hcore hstoredA hctors Aof taOf hleaf
  exact ⟨mp₁, mp₂, hE₂, hagPre, hagReal, hagC⟩

end ConLeche.Model
