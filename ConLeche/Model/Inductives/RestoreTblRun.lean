module

public import ConLeche.Model.Inductives.CopyWalkFactsAssembly
public import ConLeche.Model.Inductives.CopyCtorWalkRun
import ConLeche.Verify.Inductives.NestedCopyStored
import ConLeche.Verify.Inductives.NestedRestoreWalk
import ConLeche.Verify.Inductives.NestedLeaves
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedFields

public section

/-!
# The restore table's facts at the run (task #279 M-D′ D3, DESIGN §M.54)

`copyWalkFacts_of_run` (`CopyWalkFactsRunAssembly.lean`) opens with a
stretch of work that never looks at the constructor it is about: the
restore table `restoreTbl p st` is well-formed, its parameter count is
the datum's, its names are fresh before the block and are none of the
REAL members', every pin's copy is the block member above it, the
copies' names are distinct, no recursor name is a pin's, and every pin
is a container application whose leaves are the block's parameter
openers and which is bvar-closed.

Those facts are the whole of `RestoreTblRun` here, extracted verbatim
so that the REAL members' restored constructors (M-D′ D3) can use them
without re-deriving them per copy constructor: the run establishes the
record once (`restoreTblRun_of_run`), and `RestoreTblRun.at_openers`
reads the table's entries at ANY parameter openers off it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType NestedPin ElimState ContainerCtor AuxStored)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The record -/

/-- The restore table's facts at the run, generic in the constructor (what
`copyWalkFacts_of_run` establishes inline before its per-constructor work). -/
structure RestoreTblRun (env : Env) (p : ConLeche.NestedParts) (st : ElimState)
    (params : List Expr) (d : IndRepData V) : Prop where
  wf : (ConLeche.restoreTbl p st).WF
  nP : (ConLeche.restoreTbl p st).nP = d.nP
  auxFresh : ∀ n ∈ (ConLeche.restoreTbl p st).auxNames,
    env.find? n = none ∧ ∀ t, t < p.k → d.memberName t ≠ n
  pinName : ∀ (jq : Nat) (q : NestedPin), st.pins[jq]? = some q →
    d.memberName (p.k + jq) = q.aux
  auxNodup : (st.pins.map (·.aux)).Nodup
  recNe : ∀ q ∈ st.pins, ∀ q' ∈ st.pins, q'.aux.str "rec" ≠ q.aux
  pinShape : ∀ q ∈ st.pins, ∃ (J' : Name) (lvls' : List Level) (Ds' : List Expr),
    q.pin = Expr.mkAppN (.const J' lvls') Ds' ∧ q.container = J' ∧
    Expr.LeavesIn params q.pin ∧ q.pin.looseBVarsBounded 0 = true

/-! ## The table at a frame of parameter openers -/

omit [SetTheory V] in
/-- The table's entries at any parameter openers (fvar-shaped, one per
parameter): every pin is looked up, erased-equal to the pin, bounded; no
recursor name is a pin's. -/
theorem RestoreTblRun.at_openers {env : Env} {p : ConLeche.NestedParts} {st : ElimState}
    {params : List Expr} {d : IndRepData V} (R : RestoreTblRun env p st params d)
    {fvsP : List Expr} (hlen : fvsP.length = p.nP)
    (hshape : ∀ (k : Nat) (x : Expr), fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty) :
    (∀ q ∈ st.pins, ∃ pin',
      ((ConLeche.restoreTbl p st).instAt fvsP).pins.lookup q.aux = some pin' ∧
      Expr.ErasedEq pin' q.pin ∧ pin'.looseBVarsBounded 0 = true) ∧
    (∀ q ∈ st.pins, ((ConLeche.restoreTbl p st).instAt fvsP).recMap.lookup q.aux = none) := by
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨-, -, -, -, -, -, hB⟩ := R.pinShape q hq
    obtain ⟨pin', hlook, hE⟩ :=
      ConLeche.restoreTbl_instAt_lookup_erasedEq R.auxNodup hlen hshape hq hB
    exact ⟨pin', hlook, hE, (Expr.ErasedEq.looseBVarsBounded_iff hE 0).mpr hB⟩
  · exact ConLeche.restoreTbl_instAt_recMap (fun q' hq' => R.recNe q hq q' hq')

/-! ## The record, at the run -/

set_option maxHeartbeats 1600000 in
/-- **`RestoreTblRun` is a READ off the run**: the table's
constructor-generic facts are the block's name discipline (the formers'
front door, the block's `Nodup` names), the copies' freshness
(`copiesFresh`), the elimination's ledger (`elimNested_copy`: every pin
is a container application at bvar-closed components, minted as the
block member above it) and K.3's `pinsClosed`. -/
theorem restoreTblRun_of_run {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {fmsA ctorsA : List ConstantVal}
    {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    (hb : ConLeche.auxBlock p st = some b)
    (hlenSt : st.types.length = p.k + st.pins.length)
    (hcopies : ConLeche.copiesFresh env p.k st = true)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hpc : ConLeche.pinsClosed p.nP st.pins = true)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st)
    (hpo : PinsAtOpeners st params)
    (hhead : ∃ (t₀ : AuxType) (body body₀ : Expr), st.types[0]? = some t₀ ∧
      ConLeche.openPisAtFvars p.nP t₀.type 0 = some (params, body) ∧
      t₀.type.stripPis p.nP = some (pbs, body₀) ∧ pbs.length = p.nP ∧ t₀.type.hasFvar = false)
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d) :
    RestoreTblRun env p st params d := by
  -- the block's shape
  obtain ⟨-, hkb, hkRb, hnPb, -, -, hnames, hall⟩ := hreps
  obtain ⟨t₀, -, -, ht₀, -, -, -, -⟩ := hhead
  have hdk : d.k = p.k + st.pins.length := by rw [hkb, ConLeche.auxBlock_k hb, hlenSt]
  have hnP : d.nP = p.nP := by rw [hnPb, (ConLeche.auxBlock_inv hb).1]
  have hk0 : 0 < d.k := by
    have h0 : 0 < st.types.length := (List.getElem?_eq_some_iff.mp ht₀).1
    omega
  obtain ⟨_s₀, _cvT₀, _cvR₀, _caps₀, _mI₀, _rP₀, _rules₀, -, -, -, -, hrep₀⟩ :=
    hall 0 (by rw [← hkb]; exact hk0)
  -- the stage's formers (`CtorsChecked`)
  obtain ⟨_env₁, fms', _f₀, _ctorsA, _sortss, hformers', -, -, -, -, -⟩ := hchk
  -- the block's members are the state's types, by name
  have hmemberTy : ∀ (t : Nat) (ty : AuxType), st.types[t]? = some ty → t < d.k →
      d.memberName t = ty.name :=
    fun t ty hty ht => memberName_eq_type hb hnames hty (by rw [← hkb]; exact ht)
  have hfreshCopies := ConLeche.copiesFresh_inv hcopies
  have hdropMem : ∀ t, p.k ≤ t → t < d.k → ∃ ty, st.types[t]? = some ty ∧
      ty ∈ st.types.drop p.k := by
    intro t hkt ht
    obtain ⟨ty, hty⟩ : ∃ ty, st.types[t]? = some ty :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨ty, hty, List.mem_of_getElem? (i := t - p.k) ?_⟩
    rw [List.getElem?_drop, show p.k + (t - p.k) = t by omega]
    exact hty
  have hnodupM : ((List.range d.k).map d.memberName).Nodup := by
    have h0 := hrep₀.memberNodup
    have hkE : d.kReal = d.k := by rw [hkRb, hkb]
    rw [← hkE]
    exact h0
  -- ## every pin's copy is the block member above it (the ledger's mint)
  have hTypesLen : (ConLeche.nestedTypes0 p fmsA ctorsA).length = p.k := by
    have h1 := ConLeche.elimNested_length helim
    rw [hlenSt] at h1
    omega
  have hpinName : ∀ (jq : Nat) (qq : NestedPin), st.pins[jq]? = some qq →
      d.memberName (p.k + jq) = qq.aux := by
    intro jq qq hqq
    have hjq : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hqq).1
    obtain ⟨_t₀e, _paramse, _bodye, pbse, _body₀e, -, -, -, _Ie, _cie, _ie, _j₀e, Je, lvlse,
      Dse, qe, copye, _st₁e, _st₂e, cs'e, -, -, -, -, hqe, -, -, -, -, hmke, -, -, -, -,
      htye, -, -, -, -, -, -⟩ := ConLeche.elimNested_copy helim hjq
    have hqE : qe = qq := Option.some.inj (hqe.symm.trans hqq)
    rw [hqE] at hmke
    rw [hTypesLen] at htye
    have hname : copye.name = qq.aux := ConLeche.mkCopy_name hmke
    rw [hmemberTy _ _ htye (by omega)]
    exact hname
  -- ## the pins' shapes: a container application, at the openers, closed
  have hpinShape : ∀ qq ∈ st.pins, ∃ (J' : Name) (lvls' : List Level) (Ds' : List Expr),
      qq.pin = Expr.mkAppN (.const J' lvls') Ds' ∧ qq.container = J' ∧
      Expr.LeavesIn params qq.pin ∧ qq.pin.looseBVarsBounded 0 = true := by
    intro qq hqq
    obtain ⟨jq, hjq⟩ := List.getElem?_of_mem hqq
    have hjqlt : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hjq).1
    obtain ⟨_t₀e, _paramse, _bodye, _pbse, _body₀e, -, -, -, _Ie, _cie, _ie, _j₀e, Je, lvlse,
      Dse, qe, _copye, _st₁e, _st₂e, _cs'e, -, -, -, -, hqe, hqce, hqpe, -, -, -, hDse, -, -, -,
      -, -, -, -, -, -, -⟩ := ConLeche.elimNested_copy helim hjqlt
    have hqE : qe = qq := Option.some.inj (hqe.symm.trans hjq)
    rw [hqE] at hqce hqpe
    exact ⟨Je.name, lvlse, Dse, hqpe, hqce, hpo qq hqq,
      by rw [hqpe]; exact ConLeche.looseBVarsBounded_mkAppN rfl hDse⟩
  -- ## the formers' front door: every block name is fresh before the block
  obtain ⟨hchecksF, -⟩ := ConLeche.mutualFormers_inv hformers'
  obtain ⟨hlenFms, hposF⟩ := ConLeche.mutualFormerChecks_front hchecksF
  have hmemNameB : ∀ t, t < d.k →
      d.memberName t ∈ b.memberNames ∧ env.find? (d.memberName t) = none := by
    intro t ht
    obtain ⟨f, hft⟩ : ∃ f, fms'[t]? = some f :=
      ⟨_, List.getElem?_eq_getElem
        (show t < fms'.length by rw [hlenFms]; show t < b.k; exact hkb ▸ ht)⟩
    obtain ⟨cv, bs, hl, hff, -⟩ := hposF t f hft
    rw [hnames t (by rw [← hkb]; exact ht), memberNames_getD hl]
    exact ⟨List.mem_map_of_mem (List.mem_of_getElem? hl), hff.fresh⟩
  have hrealFresh : ∀ t, t < d.k → env.find? (d.memberName t) = none :=
    fun t ht => (hmemNameB t ht).2
  -- ## the block's names are distinct
  have hnodupB : b.blockNames.Nodup := ConLeche.nestedBlockNames_nodup hcore
  have hdisjMC : ∀ a ∈ b.memberNames, ∀ a' ∈ b.ctors.map (·.cv.name), a ≠ a' :=
    (List.nodup_append.mp (List.nodup_append.mp hnodupB).1).2.2
  have hdisjMR : ∀ a ∈ b.memberNames ++ b.ctors.map (·.cv.name),
      ∀ a' ∈ (List.range b.k).map b.recName, a ≠ a' := (List.nodup_append.mp hnodupB).2.2
  have hrecNameB : ∀ t, t < d.k →
      (d.memberName t).str "rec" ∈ (List.range b.k).map b.recName := by
    intro t ht
    obtain ⟨f, hft⟩ : ∃ f, fms'[t]? = some f :=
      ⟨_, List.getElem?_eq_getElem
        (show t < fms'.length by rw [hlenFms]; show t < b.k; exact hkb ▸ ht)⟩
    obtain ⟨cv, bs, hl, -, -⟩ := hposF t f hft
    refine List.mem_map.mpr ⟨t, List.mem_range.mpr (by rw [← hkb]; exact ht), ?_⟩
    show (b.formers.getD t default).1.name.str "rec" = _
    rw [hnames t (by rw [← hkb]; exact ht), memberNames_getD hl, List.getD_eq_getElem?_getD, hl]
    rfl
  -- ## every copy's constructor is a constructor of the block
  have hcopyCtorB : ∀ (t : Nat) (ty : AuxType), st.types[t]? = some ty → ∀ c' ∈ ty.ctors,
      c'.1 ∈ b.ctors.map (·.cv.name) := by
    intro t ty hty c' hc'
    obtain ⟨l, hl⟩ := List.getElem?_of_mem hc'
    exact List.mem_map_of_mem (List.mem_of_getElem? (ConLeche.auxBlock_ctor_getElem? hb hty hl))
  -- ## the restore table's names: fresh, and none a real member's
  have hauxFresh : ∀ n ∈ (ConLeche.restoreTbl p st).auxNames,
      env.find? n = none ∧ ∀ t, t < p.k → d.memberName t ≠ n := by
    intro n hn
    simp only [ConLeche.restoreTbl] at hn
    have hpinAux : ∀ qq ∈ st.pins, ∃ jq, jq < st.pins.length ∧ st.pins[jq]? = some qq ∧
        d.memberName (p.k + jq) = qq.aux := by
      intro qq hqq
      obtain ⟨jq, hjq⟩ := List.getElem?_of_mem hqq
      exact ⟨jq, (List.getElem?_eq_some_iff.mp hjq).1, hjq, hpinName jq qq hjq⟩
    rcases List.mem_append.mp hn with hn | hn
    · rcases List.mem_append.mp hn with hn | hn
      · obtain ⟨qq, hqq, rfl⟩ := List.mem_map.mp hn
        obtain ⟨jq, hjqlt, -, hnm⟩ := hpinAux qq hqq
        refine ⟨by rw [← hnm]; exact hrealFresh _ (by omega), fun t ht hEq => ?_⟩
        have := memberName_inj hnodupM (by omega : t < d.k) (by omega : p.k + jq < d.k)
          (by rw [hEq, hnm])
        omega
      · obtain ⟨ty, hty, hc'⟩ := List.mem_flatMap.mp hn
        obtain ⟨c', hc'mem, rfl⟩ := List.mem_map.mp hc'
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hty
        rw [List.getElem?_drop] at hi
        refine ⟨(hfreshCopies ty (List.mem_of_getElem? (by
          rw [List.getElem?_drop]; exact hi))).2.2 c' hc'mem, fun t ht hEq => ?_⟩
        refine hdisjMC _ (hmemNameB t (by omega)).1 _ ?_ hEq
        exact hcopyCtorB _ ty hi c' hc'mem
    · obtain ⟨qq, hqq, rfl⟩ := List.mem_map.mp hn
      obtain ⟨jq, hjqlt, -, hnm⟩ := hpinAux qq hqq
      obtain ⟨ty, hty, hmem⟩ := hdropMem (p.k + jq) (by omega) (by omega)
      have htyn : ty.name = qq.aux := by rw [← hmemberTy _ ty hty (by omega), hnm]
      refine ⟨by rw [← htyn]; exact (hfreshCopies ty hmem).2.1, fun t ht hEq => ?_⟩
      refine hdisjMR _ (List.mem_append_left _ (hmemNameB t (by omega)).1) _ ?_ hEq
      rw [← hnm]
      exact hrecNameB _ (by omega)
  -- ## the copies' names are the block's members above `p.k`, hence distinct
  have hauxEq : st.pins.map (·.aux) = ((List.range d.k).map d.memberName).drop p.k := by
    refine List.ext_getElem? fun i => ?_
    rw [List.getElem?_map, List.getElem?_drop, List.getElem?_map]
    by_cases hi : i < st.pins.length
    · obtain ⟨qq, hqq⟩ : ∃ qq, st.pins[i]? = some qq := ⟨_, List.getElem?_eq_getElem hi⟩
      rw [hqq, List.getElem?_range (by omega)]
      simp only [Option.map_some]
      rw [hpinName i qq hqq]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
      rfl
  have hauxNodup : (st.pins.map (·.aux)).Nodup := by
    rw [hauxEq]; exact hnodupM.sublist (List.drop_sublist _ _)
  -- ## no recursor name is a copy's
  have hrecNe : ∀ (qq : NestedPin), qq ∈ st.pins → ∀ q' ∈ st.pins, q'.aux.str "rec" ≠ qq.aux := by
    intro qq hqq q' hq' hEq
    obtain ⟨jq, hjq⟩ := List.getElem?_of_mem hqq
    obtain ⟨jq', hjq'⟩ := List.getElem?_of_mem hq'
    have hlt : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hjq).1
    have hlt' : jq' < st.pins.length := (List.getElem?_eq_some_iff.mp hjq').1
    have hm : d.memberName (p.k + jq) ∈ b.memberNames ++ b.ctors.map (·.cv.name) :=
      List.mem_append_left _ (hmemNameB _ (by omega)).1
    have hr : (d.memberName (p.k + jq')).str "rec" ∈ (List.range b.k).map b.recName :=
      hrecNameB _ (by omega)
    refine hdisjMR _ hm _ hr ?_
    rw [hpinName jq qq hjq, hpinName jq' q' hjq']
    exact hEq.symm
  -- ## the table itself
  exact
    { wf := ConLeche.restoreTbl_wf hpc (fun qq hqq => by
        obtain ⟨J', lvls', Ds', h1, -, -, -⟩ := hpinShape qq hqq
        exact ⟨J', lvls', Ds', h1⟩)
      nP := by rw [hnP]; rfl
      auxFresh := hauxFresh
      pinName := hpinName
      auxNodup := hauxNodup
      recNe := hrecNe
      pinShape := hpinShape }

end ConLeche.Model
