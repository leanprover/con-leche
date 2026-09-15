module

public import ConLeche.Model.Inductives.BlockRecCand
public import ConLeche.Model.Inductives.BlockRecFrames
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Inductives.FixRecFrames
public section

/-!
# The block's recursion kit, discharged at the datum (task #315, M3)

The candidate recursor's data (`BlockRecCand.lean`: the predecessor
map, the bound and the step) satisfy the union recursor's three
obligations (`SetModel/UnionRec.lean`) at every frame of the `k`-motive
recursor type: `PredsFrom` was `BlockRep.kitPred_from`; here the BOUND
lies in `univ ℓ` (`kitB_mem`: the frame's motive at the tuple's
spine and the value, the motive typed at `motiveAVIL`, member `c`'s
`leaf` reading the major's domain as the carrier's fibre) and the
STEP lands in the bound (`kitSt_mem`: the value decomposes by the
carrier's fixed-point equation and `fibre`; at `w ≠ 0` the decode is
the decomposition by `mkInj`, and the minor at the fields and the
inductive hypotheses folds along its type — the fields by the Π-tower,
the hypotheses by `ihPisAVM_fold_mem` with each value's membership
from `kitIhs_mem`, the conclusion by `interp_minorConcAVM` and `ctor`;
at `w = 0` — hence `ℓ = 0`, the run fact — every value is `pt` and the
bound is a truth value made true by the same fold at the real
decomposition).

**What the obligations need beyond the datum**: the recursor type's
`WellDenoted` at the frame (the run's `MutualRecData.okTy`, already a
`blockRecs` premise through `hT`).  It supplies the index readings'
FITS — a recursive field's index expressions at the target member's
index telescope (`ihDom_wd_fit`) and the constructor's result indices
at its own (`minor_conc_facts`) — which at an index sort `Prop` no
clause of the datum determines (the tuple is `pt`), and the
`Prop`-regime side conditions of every application.  The block is
needed at EVERY member (`BlockReps`): the motives and the recursive
fields range over all of them.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- **The block at every member**: each member is a stored inductive
represented at the datum — what `declBlock` installs (M4). -/
def BlockReps (m : EnvModel V env) (d : BlockRepData V) : Prop :=
  ∀ c, c < d.k → ∃ (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    BlockRep m (d.memberName c) cvT cvR mI rP rules d c

/-! ## Per-member facts -/

namespace BlockRep

variable {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
  {rules : List RecRule} {d : BlockRepData V} {mm : Nat}
  (h : BlockRep m T cvT cvR mI rP rules d mm)
include h

theorem ppsM_length (ψ : Name → Nat) : (d.ppsM mm ψ).length = d.nP + d.nIdxAt mm :=
  h.former.len ψ

theorem IdsM_length (ψ : Name → Nat) : (d.IdsM mm ψ).length = d.nIdxAt mm := by
  unfold BlockRepData.IdsM
  rw [List.length_map, List.length_drop, h.ppsM_length]
  omega

theorem ips_length (ψ : Name → Nat) : ((d.ppsM mm ψ).drop d.nP).length = d.nIdxAt mm := by
  rw [List.length_drop, h.ppsM_length]
  omega

/-- **The major's domain reads to the carrier's fibre**: the member's
former at the parameter variables (under `D` further binders) and a
fitting index spine is the carrier's component at the spine's
tuple. -/
theorem leaf_app {ψ : Name → Nat} (hpl : (d.params ψ).length = d.nP) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {is : List V} (hsp : SpineFit ρp (d.IdsM mm ψ) is)
    (as₀ : List V) :
    interp V (consList is (consList as₀ ρp))
        (AnnotTerm.mkAppN (m.acval T ψ)
          (paramBvarsAt d.nP (d.nP + (as₀.length + d.nIdxAt mm)) ++ fieldBvars (d.nIdxAt mm)))
      = SetTheory.app (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) mm) (d.tup ψ mm is) := by
  have hlen : is.length = d.nIdxAt mm := by rw [hsp.length_eq, h.IdsM_length]
  rw [interp_formerApp hlen (m.acval T ψ) (m.cval_closedL T ψ)]
  have hspP := spineFit_of_sat (Δ₀ := []) (Ds := d.params ψ) (ρ := ρp)
    (by rw [List.append_nil]; exact hρp)
  rw [hpl] at hspP
  have hfr : consList ((List.range d.nP).reverse.map ρp) (fun j => ρp (j + d.nP)) = ρp :=
    consList_range_reverse d.nP ρp
  have := h.leaf ψ (fun j => ρp (j + d.nP)) _ is hspP (by rw [hfr]; exact hsp)
  rw [hfr] at this
  exact this

/-- **A motive folded along a fitting index spine** is a graph-regime
function from the carrier's fibre into `univ ℓ`. -/
theorem motive_fold {ψ : Name → Nat} (hpl : (d.params ψ).length = d.nP) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {M : V} {elimL : Level}
    (hM : M ∈ˢ interp V ρp
      (motiveAVIL (m.acval T ψ) ψ d.nP (d.nIdxAt mm) elimL ((d.ppsM mm ψ).drop d.nP)))
    {is : List V} (hsp : SpineFit ρp (d.IdsM mm ψ) is) :
    is.foldl SetTheory.app M
      ∈ˢ piR (pwBit ψ PropWhen.never)
          (SetTheory.app (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) mm) (d.tup ψ mm is))
          (fun _ => (univ (elimL.eval ψ) : V)) := by
  unfold motiveAVIL at hM
  have hb : pwBit ψ PropWhen.never ≠ 0 := pwBit_ne_zero_of_isNever ConLeche.PropWhen.isNever_never ψ
  have hfold := mkPisAV_fold_mem (m := pwBit ψ PropWhen.never)
    (fun d' hd' => by rw [mem_rebit hd']) (fun h0 => absurd h0 hb) hM
    (by rw [rebit_map_dom]; exact hsp)
  rw [interp_pi] at hfold
  have := h.leaf_app hpl hρp hsp []
  rw [consList_nil, List.length_nil, Nat.zero_add] at this
  rw [this] at hfold
  exact hfold

/-- A motive at a fitting index spine and a value of the carrier's
fibre there is in `univ ℓ`. -/
theorem motive_app_mem {ψ : Name → Nat} (hpl : (d.params ψ).length = d.nP) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {M : V} {elimL : Level}
    (hM : M ∈ˢ interp V ρp
      (motiveAVIL (m.acval T ψ) ψ d.nP (d.nIdxAt mm) elimL ((d.ppsM mm ψ).drop d.nP)))
    {is : List V} (hsp : SpineFit ρp (d.IdsM mm ψ) is) {x : V}
    (hx : x ∈ˢ SetTheory.app (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) mm) (d.tup ψ mm is)) :
    SetTheory.app (is.foldl SetTheory.app M) x ∈ˢ (univ (elimL.eval ψ) : V) :=
  app_mem_piR_pos (pwBit_ne_zero_of_isNever ConLeche.PropWhen.isNever_never ψ) (h.motive_fold hpl hρp hM hsp) hx

end BlockRep

theorem BlockReps.params_length {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    (hk : 0 < d.k) (ψ : Name → Nat) : (d.params ψ).length = d.nP := by
  obtain ⟨_, _, _, _, _, h0⟩ := hreps 0 hk
  unfold BlockRepData.params
  rw [List.length_map, List.length_take, h0.ppsM_length]
  exact Nat.min_eq_left (Nat.le_add_right _ _)

/-! ## The bound -/

theorem BlockRepData.kitB_tagged (d : BlockRepData V) (ψ : Name → Nat) (Ms : Nat → V) (c : Nat)
    (i x : V) :
    d.kitB ψ Ms (tagged c i x)
      = SetTheory.app ((isOfW (d.uM c ψ) (d.nIdxAt c) i).foldl SetTheory.app (Ms c)) x := by
  unfold BlockRepData.kitB tagged
  rw [sfst_kpair, ssnd_kpair, natIdx_vnat, sfst_kpair, ssnd_kpair]

/-- **The bound's obligation**: at every element of the carrier's
union the bound is in `univ ℓ` — the frame's motives typed at their
readings. -/
theorem BlockReps.kitB_mem {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) {elimL : Level}
    {Ms : Nat → V}
    (hMs : ∀ c, c < d.k → Ms c ∈ˢ interp V ρp
      (motiveAVIL (m.acval (d.memberName c) ψ) ψ d.nP (d.nIdxAt c) elimL ((d.ppsM c ψ).drop d.nP))) :
    ∀ u, u ∈ˢ unionSet d.k (d.idx ψ ρp) (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) →
      d.kitB ψ Ms u ∈ˢ (univ (elimL.eval ψ) : V) := by
  intro u hu
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hpl := hreps.params_length (by omega) ψ
  have hi' : i ∈ˢ idxSet (d.uM c ψ) ρp (d.IdsM c ψ) := hi
  obtain ⟨is, hsp, rfl⟩ := mem_idxSet_elim hi'
  rw [BlockRepData.kitB_tagged, ← h.IdsM_length ψ, isOfW_tupW (h.idxOk ψ ρp hρp c hc) hsp]
  exact h.motive_app_mem hpl hρp (hMs c hc) hsp hx

/-! ## The constructors' data, per member -/

/-- **The members typed at their formers' readings** — the run's
`EnvModelM.acval_memType` at each member (a fact of the model's
invariant, not of the datum: `leaf` fixes the former at fitting spines
only).  Consumer: the index readings' fits below. -/
def FormersTyped (m : EnvModel V env) (d : BlockRepData V) (ψ : Name → Nat) : Prop :=
  ∀ t, t < d.k → ∀ ρ : Nat → V,
    interp V ρ (m.acval (d.memberName t) ψ) ∈ˢ interp V ρ (mkPisAV (d.ppsM t ψ) (.sort (d.w ψ)))

namespace BlockRep

variable {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
  {rules : List RecRule} {d : BlockRepData V} {mm : Nat}
  (h : BlockRep m T cvT cvR mI rP rules d mm)
include h

/-- Constructor `j`'s data (the block's clause at the member itself). -/
theorem ctorData {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM mm)[j]? = some cA) :
    BlockCtorData m d.env₀ (d.memberName mm) (fun i => d.memberName (d.tgts mm j i))
      (fun i => d.nIdxAt (d.tgts mm j i)) cvT.levelParams cA.1 d.nP cA.2 (d.nIdxAt mm) d.resSort
      d.isProp d.large (d.idxF mm j) (d.dsF mm j) (d.esF mm j) (d.srcsF mm j) (d.ksF mm j)
      (d.fvsPF mm j) (d.xFvsF mm j) (d.xrestF mm j) (d.eissF mm j) (d.tssF mm j) :=
  (h.ctors mm j cA h.memberLt hj).2.2

omit [SetTheory V] h in
theorem Fss_getD {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM mm)[j]? = some cA)
    (ψ : Name → Nat) : (d.Fss mm ψ).getD j [] = ((d.dsF mm j ψ).drop d.nP).map (·.2.2) :=
  fssOfR_fixCtorDataList_getD hj

omit [SetTheory V] h in
theorem Ess_getD {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM mm)[j]? = some cA)
    (ψ : Name → Nat) : (d.Ess mm ψ).getD j [] = d.esF mm j ψ :=
  essOfR_fixCtorDataList_getD hj

omit [SetTheory V] h in
theorem Eiss_getD {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM mm)[j]? = some cA)
    (ψ : Name → Nat) : (d.Eiss mm ψ).getD j [] = d.eissF mm j ψ :=
  eissOfR_fixCtorDataList_getD hj

omit [SetTheory V] h in
theorem tlss_getD {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM mm)[j]? = some cA)
    (ψ : Name → Nat) : (d.tlss mm ψ).getD j [] = d.tssF mm j ψ :=
  tlssOfR_fixCtorDataList_getD hj

omit [SetTheory V] h in
theorem rss_getD {j : Nat} (hj : j < (d.ctorsM mm).length) :
    (d.rss mm).getD j [] = rsOf (d.ksF mm j) :=
  rssOfK_getD hj

theorem Fss_length {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM mm)[j]? = some cA)
    (ψ : Name → Nat) : ((d.Fss mm ψ).getD j []).length = cA.2 := by
  rw [Fss_getD hj, List.length_map, List.length_drop, (h.ctorData hj).len]
  omega

/-- The recursive positions of constructor `j` are the kernel's. -/
theorem recIdx_eq {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM mm)[j]? = some cA)
    (ψ : Name → Nat) :
    recIdx ((d.rss mm).getD j []) ((d.Fss mm ψ).getD j []).length
      = ConLeche.recIdxOf (d.ksF mm j) := by
  rw [rss_getD (List.getElem?_eq_some_iff.mp hj).1, h.Fss_length hj, ← (h.ctorData hj).ksLen,
    recIdx_rsOf]

/-- The constructor's parameter spine at a parameter frame fits its
own parameter data. -/
theorem ctor_params_fit {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM mm)[j]? = some cA)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) :
    SpineFit (fun i => ρp (i + d.nP)) (((d.dsF mm j ψ).take d.nP).map (·.2.2))
      ((List.range d.nP).reverse.map ρp) := by
  have hsat := (h.paramsIff mm j cA h.memberLt hj ψ ρp).mp hρp
  have hlen : (((d.dsF mm j ψ).take d.nP).map (·.2.2)).length = d.nP := by
    rw [List.length_map, List.length_take, (h.ctorData hj).len]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  have := spineFit_of_sat (Δ₀ := []) (Ds := ((d.dsF mm j ψ).take d.nP).map (·.2.2)) (ρ := ρp)
    (by rw [List.append_nil]; exact hsat)
  rw [hlen] at this
  exact this

/-- **The constructor's fields are graded and its body is graded at
every fitting field spine** — its stored type's `WellDenoted` under the
parameters. -/
theorem ctor_okB {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM mm)[j]? = some cA)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) :
    FieldsOkB 0 ρp ((d.Fss mm ψ).getD j []) ∧
    ∀ fs, SpineFit ρp ((d.Fss mm ψ).getD j []) fs →
      WellDenoted V (consList fs ρp)
        (AnnotTerm.mkAppN (m.acval (d.memberName mm) ψ)
          (paramBvarsAt d.nP (d.nP + cA.2) ++ d.esF mm j ψ)) := by
  have hok := ((h.ctorData hj).okTy ψ (fun i => ρp (i + d.nP))).1
  rw [← List.take_append_drop d.nP (d.dsF mm j ψ), mkPisAV_append] at hok
  have h1 := (WellDenoted_mkPisAV_inv hok).2 _ (h.ctor_params_fit hj hρp)
  rw [consList_range_reverse] at h1
  have h2 := WellDenoted_mkPisAV_inv h1
  rw [← Fss_getD hj] at h2
  refine ⟨h2.1, fun fs hfs => ?_⟩
  have := h2.2 fs hfs
  unfold ctorBodyAVI at this
  rwa [paramBvars_eq_paramBvarsAt] at this

end BlockRep

/-! ## The index readings' fits -/

/-- **A graded application of a member's former fits its index
telescope**: the former is typed at its reading (`FormersTyped`), so
the application's `WellDenoted` package puts the parameter values and
the index readings in the former's domains. -/
theorem BlockReps.former_app_fit {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {t : Nat} (ht : t < d.k) {ρp : Nat → V}
    {as' : List V} {e : Nat} (he : as'.length = e) {Eis : List AnnotTerm}
    (hlen : Eis.length = d.nIdxAt t)
    (hwd : WellDenoted V (consList as' ρp)
      (AnnotTerm.mkAppN (m.acval (d.memberName t) ψ) (paramBvarsAt d.nP (d.nP + e) ++ Eis))) :
    SpineFit ρp (d.IdsM t ψ) (Eis.map (interp V (consList as' ρp))) := by
  obtain ⟨cvT, cvR, mI, rP, rules, ht'⟩ := hreps t ht
  have hpl : (paramBvarsAt d.nP (d.nP + e)).length = d.nP := by simp [paramBvarsAt]
  have hfit := spineFit_of_wellDenoted_mkAppN_pis (C := .sort (d.w ψ)) (ds := d.ppsM t ψ)
    (σ := fun i => ρp (i + d.nP)) (ρ := consList as' ρp) (fv := interp V (fun i => ρp (i + d.nP))
      (m.acval (d.memberName t) ψ))
    (fun d' hd' => ht'.former.bits ψ d' hd')
    (by rw [List.length_append, hpl, hlen, ht'.ppsM_length]; exact Nat.le_refl _)
    hwd (interp_closed (V := V) (m.cval_closedL _ ψ) _ _) (hfT t ht _)
  have hσ : ∀ i, consList as' ρp (i + e) = ρp i := fun i => by
    rw [← he]; exact consList_apply_add as' ρp i
  rw [List.length_append, hpl, hlen, ← ht'.ppsM_length ψ,
    List.take_length, ← List.take_append_drop d.nP (d.ppsM t ψ), List.map_append, List.map_append,
    map_paramBvarsAt_interp hσ] at hfit
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
  have hlen₁ : as₁.length = ((List.range d.nP).reverse.map ρp).length := by
    rw [h1.length_eq, List.length_map, List.length_take, ht'.ppsM_length, List.length_map,
      List.length_reverse, List.length_range]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hlen₁.symm
  rw [consList_range_reverse] at h2
  exact h2

/-- A recursive field's index expressions fit its target's index
telescope at every fitting prefix. -/
theorem BlockReps.rec_eis_fit {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {c : Nat} (hc : c < d.k) {j : Nat}
    {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {i : Nat} (hi : i < cA.2)
    (hrec : (d.ksF c j).getD i .ordinary = .recursive) {fs' : List V}
    (hfs' : SpineFit ρp (((d.Fss c ψ).getD j []).take i) fs') :
    SpineFit ρp (d.IdsM (d.tgts c j i) ψ)
      (((d.eissF c j ψ).getD i []).map (interp V (consList fs' ρp))) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hlenF := h.Fss_length hj ψ
  have hwd := fieldsOkB_getD (h.ctor_okB hj hρp).1 (j := i) (by rw [hlenF]; exact hi) hfs'
  rw [BlockRep.Fss_getD hj, fields_getD (by rw [List.length_drop, hcd.len]; omega),
    List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
    hcd.recEntry ψ i hrec hi] at hwd
  have hlen' : fs'.length = i := by
    rw [hfs'.length_eq, List.length_take, hlenF]; exact Nat.min_eq_left (Nat.le_of_lt hi)
  exact hreps.former_app_fit hfT (h.tgtsLt c j i hc (List.getElem?_eq_some_iff.mp hj).1
    (by rw [hcd.ksLen]; exact hi)) hlen' (hcd.eisLen ψ i hrec hi) hwd

/-- A reflexive field's index expressions fit its target's index
telescope at every fitting prefix and telescope spine. -/
theorem BlockReps.refl_eis_fit {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {c : Nat} (hc : c < d.k) {j : Nat}
    {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {i : Nat} (hi : i < cA.2)
    (hrefl : (d.ksF c j).getD i .ordinary = .reflexive) {fs' : List V}
    (hfs' : SpineFit ρp (((d.Fss c ψ).getD j []).take i) fs') {bs : List V}
    (hbs : SpineFit (consList fs' ρp) (((d.tssF c j ψ).getD i []).map (·.2.2)) bs) :
    SpineFit ρp (d.IdsM (d.tgts c j i) ψ)
      (((d.eissF c j ψ).getD i []).map (interp V (consList bs (consList fs' ρp)))) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hlenF := h.Fss_length hj ψ
  have hwd := fieldsOkB_getD (h.ctor_okB hj hρp).1 (j := i) (by rw [hlenF]; exact hi) hfs'
  rw [BlockRep.Fss_getD hj, fields_getD (by rw [List.length_drop, hcd.len]; omega),
    List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
    hcd.reflEntry ψ i hrefl hi] at hwd
  have hlen' : fs'.length = i := by
    rw [hfs'.length_eq, List.length_take, hlenF]; exact Nat.min_eq_left (Nat.le_of_lt hi)
  have hwd' := (WellDenoted_mkPisAV_inv hwd).2 bs hbs
  rw [← consList_append, Nat.add_assoc] at hwd'
  have := hreps.former_app_fit hfT (h.tgtsLt c j i hc (List.getElem?_eq_some_iff.mp hj).1
    (by rw [hcd.ksLen]; exact hi))
    (by rw [List.length_append, hlen', hbs.length_eq, List.length_map])
    (hcd.eisLenRefl ψ i hrefl hi) hwd'
  rwa [consList_append] at this

/-- The constructor's result index readings fit its member's index
telescope at every fitting field spine. -/
theorem BlockReps.res_es_fit {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {c : Nat} (hc : c < d.k) {j : Nat}
    {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {fs : List V}
    (hfs : SpineFit ρp ((d.Fss c ψ).getD j []) fs) :
    SpineFit ρp (d.IdsM c ψ) ((d.esF c j ψ).map (interp V (consList fs ρp))) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hwd := (h.ctor_okB hj hρp).2 fs hfs
  have hlen : fs.length = cA.2 := by rw [hfs.length_eq, h.Fss_length hj]
  exact hreps.former_app_fit hfT hc hlen ((h.ctorData hj).lenE ψ) hwd

/-! ## The recursive slots are the fields' real domains -/

theorem spineFit_take' {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) {i : Nat} (hi : i ≤ Fs.length) :
    SpineFit ρ (Fs.take i) (as.take i) := by
  have h' : SpineFit ρ (Fs.take i ++ Fs.drop i) as := by rw [List.take_append_drop]; exact h
  obtain ⟨as₁, as₂, heq, h1, -⟩ := spineFit_append_inv h'
  have hl : as₁.length = i := by
    rw [h1.length_eq, List.length_take]; exact Nat.min_eq_left hi
  have : as.take i = as₁ := by
    rw [heq, List.take_append, List.take_of_length_le (Nat.le_of_eq hl), hl, Nat.sub_self,
      List.take_zero, List.append_nil]
  rw [this]
  exact h1

namespace BlockRep

variable {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
  {rules : List RecRule} {d : BlockRepData V} {mm : Nat}
  (h : BlockRep m T cvT cvR mI rP rules d mm)
include h

/-- `leaf_app` at index EXPRESSIONS: the former at the parameter
variables and fitting index readings is the carrier's fibre at the
readings' tuple. -/
theorem leaf_app' {ψ : Name → Nat} (hpl : (d.params ψ).length = d.nP) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {as₀ : List V} {e : Nat} (he : as₀.length = e)
    {Eis : List AnnotTerm} (hfit : SpineFit ρp (d.IdsM mm ψ) (Eis.map (interp V (consList as₀ ρp)))) :
    interp V (consList as₀ ρp) (AnnotTerm.mkAppN (m.acval T ψ) (paramBvarsAt d.nP (d.nP + e) ++ Eis))
      = SetTheory.app (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) mm)
          (d.tup ψ mm (Eis.map (interp V (consList as₀ ρp)))) := by
  subst he
  rw [interp_formerApp' (m.acval T ψ) (m.cval_closedL T ψ)]
  have hspP := spineFit_of_sat (Δ₀ := []) (Ds := d.params ψ) (ρ := ρp)
    (by rw [List.append_nil]; exact hρp)
  rw [hpl] at hspP
  have hfr : consList ((List.range d.nP).reverse.map ρp) (fun j => ρp (j + d.nP)) = ρp :=
    consList_range_reverse d.nP ρp
  have := h.leaf ψ (fun j => ρp (j + d.nP)) _ _ hspP (by rw [hfr]; exact hfit)
  rw [hfr] at this
  exact this

end BlockRep

/-- **A recursive or reflexive field's real domain is its slot at the
carrier** — the field's entry reads to the slot set at the block's
least tuple, at every fitting prefix. -/
theorem BlockReps.real_dom_eq {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {c : Nat} (hc : c < d.k) {j : Nat}
    {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {i : Nat} (hi : i < cA.2)
    (hr : (rsOf (d.ksF c j)).getD i false = true) {fs' : List V}
    (hfs' : SpineFit ρp (((d.Fss c ψ).getD j []).take i) fs') :
    interp V (consList fs' ρp) (((d.Fss c ψ).getD j []).getD i default)
      = d.slotAt ψ (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c j i (consList fs' ρp) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hpl := hreps.params_length (by omega) ψ
  have hlenF := h.Fss_length hj ψ
  have hlen' : fs'.length = i := by
    rw [hfs'.length_eq, List.length_take, hlenF]; exact Nat.min_eq_left (Nat.le_of_lt hi)
  have htgt := h.tgtsLt c j i hc (List.getElem?_eq_some_iff.mp hj).1 (by rw [hcd.ksLen]; exact hi)
  obtain ⟨cvT', cvR', mI', rP', rules', ht⟩ := hreps _ htgt
  have hiK : i < (d.ksF c j).length := by rw [hcd.ksLen]; exact hi
  unfold BlockRepData.slotAt
  rw [BlockRep.tlss_getD hj, BlockRep.Eiss_getD hj, BlockRep.Fss_getD hj,
    fields_getD (by rw [List.length_drop, hcd.len]; omega), List.getD_eq_getElem?_getD,
    List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  have hk : (d.ksF c j).getD i .ordinary = .recursive ∨ (d.ksF c j).getD i .ordinary = .reflexive := by
    unfold rsOf at hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hiK,
      Option.map_some, Option.getD_some, decide_eq_true_iff] at hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiK]
    exact hr
  rcases hk with hk | hk
  · -- finitary: the slot is the fibre at the readings' tuple
    rw [hcd.tssNone ψ i (by rw [hk]; decide), slotSet_nil, hcd.recEntry ψ i hk hi]
    exact ht.leaf_app' hpl hρp hlen' (hreps.rec_eis_fit hfT hc hj hρp hi hk hfs')
  · -- reflexive: the nested product over the telescope of the fibre
    rw [hcd.reflEntry ψ i hk hi]
    unfold slotSet
    refine ConLeche.Semantics.interp_mkPisAV_piTele (v := d.w ψ) (acc := [])
      (fun d' hd' => hcd.tssBits ψ i d' hd') fun bs hbs => ?_
    rw [List.nil_append, ← consList_append, Nat.add_assoc]
    exact ht.leaf_app' hpl hρp
      (as₀ := fs' ++ bs) (e := i + ((d.tssF c j ψ).getD i []).length)
      (by rw [List.length_append, hlen', hbs.length_eq, List.length_map])
      (by rw [consList_append]; exact hreps.refl_eis_fit hfT hc hj hρp hi hk hfs' hbs)

/-- A recursive slot at a tuple below the carrier is within the slot at
the carrier. -/
theorem BlockReps.slotAt_mono {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {c : Nat} (hc : c < d.k) {j : Nat}
    {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {i : Nat} (hi : i < cA.2)
    (hr : (rsOf (d.ksF c j)).getD i false = true) {fs' : List V}
    (hfs' : SpineFit ρp (((d.Fss c ψ).getD j []).take i) fs') {X : Nat → V}
    (hX : TupleLe d.k (d.idx ψ ρp) X (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp))) :
    d.slotAt ψ X c j i (consList fs' ρp)
      ⊆ˢ d.slotAt ψ (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c j i (consList fs' ρp) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hlenF := h.Fss_length hj ψ
  have hiK : i < (d.ksF c j).length := by rw [hcd.ksLen]; exact hi
  have htgt := h.tgtsLt c j i hc (List.getElem?_eq_some_iff.mp hj).1 hiK
  have hk : (d.ksF c j).getD i .ordinary = .recursive ∨ (d.ksF c j).getD i .ordinary = .reflexive := by
    unfold rsOf at hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hiK,
      Option.map_some, Option.getD_some, decide_eq_true_iff] at hr
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiK]
    exact hr
  unfold BlockRepData.slotAt slotSet
  rw [BlockRep.tlss_getD hj, BlockRep.Eiss_getD hj]
  refine piTele_mono fun bs hbs => ?_
  rw [List.nil_append]
  refine hX _ htgt _ ?_
  rw [fitsS_teleOfFields] at hbs
  rcases hk with hk | hk
  · rw [hcd.tssNone ψ i (by rw [hk]; decide)] at hbs
    cases bs with
    | nil => exact tupW_mem (hreps.rec_eis_fit hfT hc hj hρp hi hk hfs')
    | cons _ _ => exact hbs.elim
  · exact tupW_mem (hreps.refl_eis_fit hfT hc hj hρp hi hk hfs' hbs)

/-- **A fit at the slots of a tuple below the carrier fits the real
domains** (the slot is within the real domain). -/
theorem BlockReps.spineFit_of_fitsFrom_go {m : EnvModel V env} {d : BlockRepData V}
    (hreps : BlockReps m d) {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {c : Nat} (hc : c < d.k)
    {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {X : Nat → V}
    (hX : TupleLe d.k (d.idx ψ ρp) X (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp))) :
    ∀ (rest : List AnnotTerm) (i : Nat) (fs' as : List V),
      ((d.Fss c ψ).getD j []).drop i = rest →
      SpineFit ρp (((d.Fss c ψ).getD j []).take i) fs' →
      FitsFrom ((d.rss c).getD j []) (d.slotAt ψ X c j) i (consList fs' ρp) rest as →
      SpineFit (consList fs' ρp) rest as
  | [], _, _, [], _, _, _ => trivial
  | [], _, _, _ :: _, _, _, hf => hf.elim
  | _ :: _, _, _, [], _, _, hf => hf.elim
  | F :: rest, i, fs', a :: as, hdrop, hfs', hf => by
    obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
    have hlenF := h.Fss_length hj ψ
    have hi : i < ((d.Fss c ψ).getD j []).length := by
      rcases Nat.lt_or_ge i ((d.Fss c ψ).getD j []).length with hi | hi
      · exact hi
      · rw [List.drop_eq_nil_of_le hi] at hdrop; exact nomatch hdrop
    have hFi : ((d.Fss c ψ).getD j [])[i]? = some F := by
      have := List.getElem?_drop (xs := (d.Fss c ψ).getD j []) (i := i) (j := 0)
      rw [hdrop, Nat.add_zero] at this
      exact this.symm
    have hF : ((d.Fss c ψ).getD j []).getD i default = F := by
      rw [List.getD_eq_getElem?_getD, hFi]; rfl
    obtain ⟨ha, hrest⟩ := hf
    have hmem : a ∈ˢ interp V (consList fs' ρp) F := by
      rw [BlockRep.rss_getD (List.getElem?_eq_some_iff.mp hj).1] at ha
      split at ha
      · next hr =>
        rw [← hF, hreps.real_dom_eq hfT hc hj hρp (by rw [← hlenF]; exact hi) hr hfs']
        exact hreps.slotAt_mono hfT hc hj hρp (by rw [← hlenF]; exact hi) hr hfs' hX a ha
      · exact ha
    refine ⟨hmem, ?_⟩
    have hfs'' : SpineFit ρp (((d.Fss c ψ).getD j []).take (i + 1)) (fs' ++ [a]) := by
      rw [List.take_add_one, hFi, Option.toList_some]
      exact hfs'.append ⟨hmem, trivial⟩
    have := hreps.spineFit_of_fitsFrom_go hfT hc hj hρp hX rest (i + 1) (fs' ++ [a]) as
      (by rw [← List.drop_drop, hdrop]; rfl) hfs''
      (by rw [consList_append, consList_cons, consList_nil]; exact hrest)
    rw [consList_append, consList_cons, consList_nil] at this
    exact this

theorem BlockReps.spineFit_of_fitsFrom {m : EnvModel V env} {d : BlockRepData V}
    (hreps : BlockReps m d) {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {c : Nat} (hc : c < d.k)
    {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {X : Nat → V}
    (hX : TupleLe d.k (d.idx ψ ρp) X (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp))) {fs : List V}
    (hf : FitsFrom ((d.rss c).getD j []) (d.slotAt ψ X c j) 0 ρp ((d.Fss c ψ).getD j []) fs) :
    SpineFit ρp ((d.Fss c ψ).getD j []) fs := by
  have := hreps.spineFit_of_fitsFrom_go hfT hc hj hρp hX _ 0 [] fs rfl trivial
    (by rw [consList_nil]; exact hf)
  rwa [consList_nil] at this

/-- **A fit at the real domains fits the slots at the carrier.** -/
theorem BlockReps.fitsFrom_of_spineFit_go {m : EnvModel V env} {d : BlockRepData V}
    (hreps : BlockReps m d) {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {c : Nat} (hc : c < d.k)
    {j : Nat} {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) :
    ∀ (rest : List AnnotTerm) (i : Nat) (fs' as : List V),
      ((d.Fss c ψ).getD j []).drop i = rest →
      SpineFit ρp (((d.Fss c ψ).getD j []).take i) fs' →
      SpineFit (consList fs' ρp) rest as →
      FitsFrom ((d.rss c).getD j []) (d.slotAt ψ (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c j)
        i (consList fs' ρp) rest as
  | [], _, _, [], _, _, _ => trivial
  | [], _, _, _ :: _, _, _, hf => hf.elim
  | _ :: _, _, _, [], _, _, hf => hf.elim
  | F :: rest, i, fs', a :: as, hdrop, hfs', hf => by
    obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
    have hlenF := h.Fss_length hj ψ
    have hi : i < ((d.Fss c ψ).getD j []).length := by
      rcases Nat.lt_or_ge i ((d.Fss c ψ).getD j []).length with hi | hi
      · exact hi
      · rw [List.drop_eq_nil_of_le hi] at hdrop; exact nomatch hdrop
    have hFi : ((d.Fss c ψ).getD j [])[i]? = some F := by
      have := List.getElem?_drop (xs := (d.Fss c ψ).getD j []) (i := i) (j := 0)
      rw [hdrop, Nat.add_zero] at this
      exact this.symm
    have hF : ((d.Fss c ψ).getD j []).getD i default = F := by
      rw [List.getD_eq_getElem?_getD, hFi]; rfl
    obtain ⟨ha, hrest⟩ := hf
    refine ⟨?_, ?_⟩
    · rw [BlockRep.rss_getD (List.getElem?_eq_some_iff.mp hj).1]
      split
      · next hr =>
        rw [← hreps.real_dom_eq hfT hc hj hρp (by rw [← hlenF]; exact hi) hr hfs', hF]
        exact ha
      · exact ha
    · have hfs'' : SpineFit ρp (((d.Fss c ψ).getD j []).take (i + 1)) (fs' ++ [a]) := by
        rw [List.take_add_one, hFi, Option.toList_some]
        exact hfs'.append ⟨ha, trivial⟩
      have := hreps.fitsFrom_of_spineFit_go hfT hc hj hρp rest (i + 1) (fs' ++ [a]) as
        (by rw [← List.drop_drop, hdrop]; rfl) hfs''
        (by rw [consList_append, consList_cons, consList_nil]; exact hrest)
      rw [consList_append, consList_cons, consList_nil] at this
      exact this

/-- **The fibre's converse**: a constructor's injection at a fitting
field spine is in the carrier's fibre at the tuple of its result index
readings. -/
theorem BlockReps.inj_mem {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} (hfT : FormersTyped m d ψ) {c : Nat} (hc : c < d.k) {j : Nat}
    {cA : ConstantVal × Nat} (hj : (d.ctorsM c)[j]? = some cA) {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {fs : List V}
    (hfs : SpineFit ρp ((d.Fss c ψ).getD j []) fs) :
    d.inj ψ c j fs ∈ˢ SetTheory.app (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) c)
      (d.tup ψ c ((d.esF c j ψ).map (interp V (consList fs ρp)))) := by
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hEs := hreps.res_es_fit hfT hc hj hρp hfs
  have ht : d.tup ψ c ((d.esF c j ψ).map (interp V (consList fs ρp))) ∈ˢ d.idx ψ ρp c := tupW_mem hEs
  rw [← h.carrier_app_eq hρp hc ht]
  refine (h.fibre ψ ρp hρp _ (lfpTuple_mem _ _ _ _) c hc _ ht _).mpr
    ⟨j, fs, (List.getElem?_eq_some_iff.mp hj).1, ⟨?_, ?_⟩, rfl⟩
  · have := hreps.fitsFrom_of_spineFit_go hfT hc hj hρp _ 0 [] fs rfl trivial
      (by rw [consList_nil]; exact hfs)
    rwa [consList_nil] at this
  · intro l hl
    rw [h.IdsM_length] at hl
    have hlenE : ((d.esF c j ψ).map (interp V (consList fs ρp))).length = d.nIdxAt c := by
      rw [List.length_map, hcd.lenE]
    have hgetD : interp V (consList fs ρp) (((d.Ess c ψ).getD j []).getD l default)
        = ((d.esF c j ψ).map (interp V (consList fs ρp))).getD l pt := by
      rw [BlockRep.Ess_getD hj, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_getElem (by rw [hcd.lenE]; exact hl), Option.map_some,
        Option.getD_some, Option.getD_some]
    rw [hgetD]
    unfold BlockRepData.tup
    by_cases hu : d.uM c ψ = 0
    · rw [tupW, if_pos hu, Tower.projS_pt]
      have hrep := spineFit_zero_replicate (hu ▸ (h.idxOk ψ ρp hρp c hc).2) hEs
      rw [hrep, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [List.length_replicate, h.IdsM_length]; exact hl)]
      simp
    · rw [tupW, if_neg hu, Tower.projS_mkTower l _ (by rw [hlenE]; exact hl),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenE]; exact hl),
        Option.getD_some]

/-! ## The block's minor index -/

omit [SetTheory V] in
theorem sum_range_lt (f : Nat → Nat) : ∀ (k c : Nat), c < k →
    ((List.range c).map f).sum + f c ≤ ((List.range k).map f).sum
  | 0, _, hc => absurd hc (Nat.not_lt_zero _)
  | k + 1, c, hc => by
    rw [List.range_succ, List.map_append, List.sum_append]
    rcases Nat.lt_or_ge c k with hck | hck
    · have := sum_range_lt f k c hck
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    · have : c = k := by omega
      subst this
      simp

omit [SetTheory V] in
/-- The block's minor index of a member's constructor is within the
block's minors. -/
theorem BlockRepData.minorIdx_lt (d : BlockRepData V) {c j : Nat} (hc : c < d.k)
    (hj : j < (d.ctorsM c).length) : d.minorIdx c j < d.nCtors := by
  unfold BlockRepData.minorIdx BlockRepData.nCtors
  have := sum_range_lt (fun t => (d.ctorsM t).length) d.k c hc
  omega

end ConLeche.Model
