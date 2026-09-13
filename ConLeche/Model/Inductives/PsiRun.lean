module

public import ConLeche.Model.Inductives.PsiAssembly
public import ConLeche.Model.Inductives.CopyReads
import ConLeche.Model.Inductives.SumRecRead
import ConLeche.Verify.Inductives.NestedLeaves
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Level

public section

/-!
# ψ at the RUN level: the pins' group facts from `DeclNestedRun` (task #279 M-B′, DESIGN §M.28)

`PsiAssembly.lean` closes ψ at the DATUM level: `psiFold_typed` gives
`PsiTypedPi` at every pin from the group facts of every pin
(`GroupFacts`) and the bridge to the order's relation.  This module
reads the group facts off the run:

* **`ContainersRep`** — the container-side premise (the successor of
  `ContainersAt`): every container the elimination recovers is
  REPRESENTED at the scratch environment by one datum per block, with
  a non-nested container's view identities, its recursor stored with
  rules, its elimination universe fresh in its level parameters, and
  a small-eliminating block Prop-valued.  It comes through the
  modelled route's `ModeledLeaf` disjunct until that route is deleted
  (DESIGN §M.19), so it stays a named premise here.
* **`pinAssign`** — the pin's level assignment: the container's
  parameters at the pin's levels (`Level.substFn`, what the copy's
  stored type reads at) and the elimination universe at the carrier's
  rank (`GroupFacts.lev`, the choice `psiSetup_of_group` needs); the
  readings the pin fixes see no difference (`acval_params`,
  `FormerData.params`).
* **`PinFacts`** — `GroupFacts` without its constructor field: what
  the pin's read and the container's representation give; and
  **`pinFacts_of_run`** — every pin has them, with one `CopyData` per
  pin (`cd`), the group base and member the ledger's, the readings the
  pin's inference's (`DenoteMetaSpine`, the same for a whole group).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType NestedPin ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The sort transfers -/

/-- `FormerFacts` across the block's re-sorting. -/
theorem FormerFacts.congr_sort {d : IndRepData V} {s s' : Level}
    (hs : ∀ φ : Name → Nat, s.eval φ = s'.eval φ) {m : EnvModel V env} {ψ : Name → Nat} {t : Nat}
    (h : ({d with resSort := s} : IndRepData V).FormerFacts m ψ t) :
    ({d with resSort := s'} : IndRepData V).FormerFacts m ψ t := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun ρ => ?_, fun ρ => ?_⟩
  · have := h3 ρ
    show interp V ρ (m.acval (d.memberName t) ψ)
      ∈ˢ interp V ρ (mkPisAV (d.ppsM t ψ) (.sort (s'.eval ψ)))
    rw [← hs ψ]
    exact this
  · have := h4 ρ
    show WellDenotedV V ρ (mkPisAV (d.ppsM t ψ) (.sort (s'.eval ψ)))
    rw [← hs ψ]
    exact this

/-- `LeafShape` across the block's re-sorting. -/
theorem LeafShape.congr_sort {d : IndRepData V} {s s' : Level}
    (hs : ∀ φ : Name → Nat, s.eval φ = s'.eval φ) {m : EnvModel V env} {ψ : Name → Nat} {t : Nat}
    (h : ({d with resSort := s} : IndRepData V).LeafShape m ψ t) :
    ({d with resSort := s'} : IndRepData V).LeafShape m ψ t := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, ?_⟩
  show m.acval (d.memberName t) ψ = mkLamsC (s'.eval ψ + 1) (d.ppsM t ψ) B
  rw [← hs ψ]
  exact hB

/-! ## The container-side premise -/

/-- The position of constructor `Jc` among its own member's
constructors: the earlier constructors of the same member. -/
@[expose] def posIn (dJ : IndRepData V) (Jc : Nat) : Nat :=
  ((List.range Jc).filter fun i => dJ.mems i == dJ.mems Jc).length

omit [SetTheory V] in
/-- `posIn` grows strictly along a member's constructors (task #279
M-C′ step 5: the position recovers the constructor within its member). -/
theorem posIn_lt_of_lt (dJ : IndRepData V) {Jc J : Nat} (hlt : Jc < J)
    (hm : dJ.mems Jc = dJ.mems J) : posIn dJ Jc < posIn dJ J := by
  unfold posIn
  suffices h : ∀ n, Jc < n →
      ((List.range Jc).filter fun i => dJ.mems i == dJ.mems Jc).length + 1
        ≤ ((List.range n).filter fun i => dJ.mems i == dJ.mems J).length from h J hlt
  intro n hn
  induction n with
  | zero => exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append]
    rcases Nat.lt_or_ge Jc n with h | h
    · have := ih h
      omega
    · obtain rfl : Jc = n := by omega
      rw [List.filter_congr (fun x _ => by rw [hm] :
        ∀ x ∈ List.range Jc, (dJ.mems x == dJ.mems Jc) = (dJ.mems x == dJ.mems J))]
      simp only [List.filter_cons, List.filter_nil, hm, beq_self_eq_true]
      exact Nat.le_refl _

omit [SetTheory V] in
/-- `posIn` is injective within a member. -/
theorem posIn_inj (dJ : IndRepData V) {Jc J : Nat} (hm : dJ.mems Jc = dJ.mems J)
    (h : posIn dJ Jc = posIn dJ J) : Jc = J := by
  rcases Nat.lt_trichotomy Jc J with hlt | rfl | hlt
  · have := posIn_lt_of_lt dJ hlt hm
    omega
  · rfl
  · have := posIn_lt_of_lt dJ hlt hm.symm
    omega

/-- **The container's constructors as `containerInfo?` read them are
the datum's**: every constructor `Jc` of the datum is, at its member
`dJ.mems Jc`, the `posIn dJ Jc`-th constructor `containerInfo?` lists
for that member — the same name, stored type and field count — and
every listed constructor is such a `Jc`.  (A container's
`containerInfo?` lists a member's constructors as its recursor's
rules, in order; the datum's are the block's in order.) -/
structure ContainerCtorsAt (ci : ContainerInfo) (dJ : IndRepData V) : Prop where
  fwd : ∀ (Jc : Nat) (cAJ : ConstantVal × Nat), dJ.ctorsA[Jc]? = some cAJ →
    ∃ (J : ContainerMember) (c : ConLeche.ContainerCtor), ci.members[dJ.mems Jc]? = some J ∧
      J.ctors[posIn dJ Jc]? = some c ∧ cAJ.1.name = c.name ∧ cAJ.1.type = c.type ∧
      cAJ.2 = c.nFields
  /-- and conversely every listed constructor of a member is one of the
  datum's at that member and position (the datum's constructors of a
  member are its recursor's rules, `IndRep.rules`, which is what
  `containerInfo?` lists — task #279 M-C′, the ψ⁻¹ side's heads) -/
  inv : ∀ (mm l : Nat) (J : ContainerMember) (c : ConLeche.ContainerCtor),
    ci.members[mm]? = some J → J.ctors[l]? = some c →
    ∃ (Jc : Nat) (cAJ : ConstantVal × Nat), dJ.ctorsA[Jc]? = some cAJ ∧ dJ.mems Jc = mm ∧
      posIn dJ Jc = l

/-- **The containers are represented at the scratch environment**: for
every container `I` the elimination recovers (`containerInfo?` at the
pre-block environment) there is ONE datum `dJ` of its block — a
non-nested container's (empty `ctorsC`, every member real, the pins the
parameters, the recursor view the functor view), a small-eliminating
block Prop-valued — such that every member `i` of the group is
`IndRep` at member `i` of `dJ`: stored at the scratch environment with
the type and level parameters `containerInfo?` read, its recursor
stored with rules, its elimination universe not among its level
parameters.  A named premise (the `ModeledLeaf` disjunct, DESIGN §M.19)
until the modelled route goes. -/
def ContainersRep (env envAux : Env) (m : EnvModel V envAux) : Prop :=
  ∀ (I : Name) (ci : ContainerInfo), ConLeche.containerInfo? env I = some ci →
    ∃ dJ : IndRepData V,
      dJ.ctorsC = [] ∧ dJ.kReal = dJ.k ∧ ci.nP = dJ.nP ∧ ci.members.length = dJ.k ∧
      (∀ (t : Nat) (φ : Name → Nat), dJ.pinsAV t φ = paramBvarsAt dJ.nP dJ.nP) ∧
      (∀ J, dJ.ksR J = dJ.ksF J ∧ dJ.tgtsR J = dJ.tgts J ∧ dJ.eissR J = dJ.eissF J ∧
        dJ.tssR J = dJ.tssF J) ∧
      (dJ.large = false → ∀ φ : Name → Nat, dJ.w φ = 0) ∧
      ContainerCtorsAt ci dJ ∧
      ∀ (i : Nat) (J : ContainerMember), ci.members[i]? = some J →
        ∃ (cvTJ cvR : ConstantVal) (capsJ : IndCaps) (mI rP : Nat) (rules : List RecRule),
          envAux.find? J.name = some (.indInfo cvTJ capsJ) ∧ J.type = cvTJ.type ∧
          J.lps = cvTJ.levelParams ∧ rules ≠ [] ∧
          envAux.find? cvR.name = some (.recInfo cvR mI rP rules) ∧
          (dJ.large = true → dJ.elim ∉ cvTJ.levelParams) ∧
          IndRep m J.name cvTJ cvR mI rP rules dJ i

/-! ## The pin's level assignment -/

/-- The pin's level assignment: the container's parameters at the pin's
levels, and the elimination universe (when the container eliminates
largely) at the carrier's rank. -/
@[expose] def pinAssign (dJ : IndRepData V) (ψ' : Name → Nat) : Name → Nat :=
  fun q => if dJ.large = true ∧ q = dJ.elim then dJ.w ψ' else ψ' q

omit [SetTheory V] in
/-- The assignment agrees with the pin's substitution on the container's
level parameters. -/
theorem pinAssign_agree {dJ : IndRepData V} {ψ' : Name → Nat} {lps : List Name}
    (hfresh : dJ.large = true → dJ.elim ∉ lps) : ∀ q ∈ lps, pinAssign dJ ψ' q = ψ' q := by
  intro q hq
  unfold pinAssign
  split
  · next h =>
    exfalso
    exact hfresh h.1 (h.2 ▸ hq)
  · rfl

omit [SetTheory V] in
/-- The elimination universe reads as the carrier's rank at the pin's
assignment, given the carrier's rank reads alike at the two
(`FormerData.params` at the member's stored former). -/
theorem pinAssign_lev {dJ : IndRepData V} {ψ' : Name → Nat}
    (hw : dJ.w (pinAssign dJ ψ') = dJ.w ψ')
    (hprop : dJ.large = false → ∀ φ : Name → Nat, dJ.w φ = 0) :
    dJ.elimL.eval (pinAssign dJ ψ') = dJ.w (pinAssign dJ ψ') := by
  unfold IndRepData.elimL ConLeche.structElimLevel
  cases hl : dJ.large with
  | true =>
    simp only [if_true, Level.eval]
    have h1 : pinAssign dJ ψ' dJ.elim = dJ.w ψ' := by
      unfold pinAssign
      rw [if_pos ⟨hl, rfl⟩]
    rw [h1, hw]
  | false =>
    simp only [Bool.false_eq_true, if_false, Level.eval]
    exact (hprop hl _).symm

/-! ## The pin's facts -/

/-- **A pin's group facts without its constructor field** — what the
pin's read and the container's representation give of
`GroupFacts` (`PsiAssembly.lean`). -/
structure PinFacts {μ : CheckMode} (mp : EnvModelM V μ env) (d : IndRepData V) (ψ : Name → Nat)
    (k₀ : Nat) (c : CopyData V) : Prop where
  mm : c.mm < c.dJ.k
  ctorsC : c.dJ.ctorsC = []
  kReal : c.dJ.kReal = c.dJ.k
  pinsAV : ∀ (t : Nat) (φ : Name → Nat), c.dJ.pinsAV t φ = paramBvarsAt c.dJ.nP c.dJ.nP
  view : ∀ J, c.dJ.ksR J = c.dJ.ksF J ∧ c.dJ.tgtsR J = c.dJ.tgts J ∧ c.dJ.eissR J = c.dJ.eissF J ∧
    c.dJ.tssR J = c.dJ.tssF J
  rep : ∃ (T : Name) (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule) (t₀ : Nat),
    t₀ < c.dJ.k ∧ rules ≠ [] ∧ env.find? cvR.name = some (.recInfo cvR mI rP rules) ∧
    IndRep mp.base2 T cvT cvR mI rP rules c.dJ t₀
  /-- every member of the container's group is represented at the
  datum (task #279 M-C′: the round trips' inductions run at every
  member) -/
  repAll : ∀ t, t < c.dJ.k → ∃ (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    IndRep mp.base2 (c.dJ.memberName t) cvT cvR mI rP rules c.dJ t
  len : c.DsA.length = c.dJ.nP
  lev : c.dJ.elimL.eval c.ψ' = c.dJ.w c.ψ'
  kA : ∀ t, t < c.dJ.k → k₀ + c.base + t < d.k
  grp : ∀ t, t < c.dJ.k → CopyData.Ok mp.base2 d ψ k₀ (c.base + t) ⟨c.dJ, t, c.ψ', c.DsA, c.base⟩

/-- `GroupFacts` from `PinFacts` and the constructor field. -/
theorem GroupFacts.of_pinFacts {μ : CheckMode} {mp : EnvModelM V μ env} {d : IndRepData V}
    {ψ : Name → Nat} {k₀ : Nat} {lpsT : List Name} {cd : Nat → CopyData V} {c : CopyData V}
    {auxOf : Nat → Nat} (pf : PinFacts mp d ψ k₀ c)
    (hctors : ∀ Jc cAJ, c.dJ.ctorsA[Jc]? = some cAJ → ∃ cAa, d.ctorsA[auxOf Jc]? = some cAa ∧
      CopyCtorFacts mp.base2 d c.dJ ψ c.ψ' c.DsA k₀ c.base cd lpsT Jc (auxOf Jc) cAJ cAa) :
    GroupFacts mp d ψ k₀ lpsT cd c auxOf :=
  ⟨pf.mm, pf.ctorsC, pf.kReal, pf.pinsAV, pf.view, pf.rep, pf.len, pf.lev, pf.kA, pf.grp, hctors⟩

/-- The two readings of a pin's components agree. -/
theorem denoteMetaSpine_eq {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}
    {n : Nat} {as : List Expr} {vs vs' : List AnnotTerm}
    (h : DenoteMetaSpine acval env φ n as vs) (h' : DenoteMetaSpine acval env φ n as vs') :
    vs = vs' :=
  DenoteMetaSpine.unique h h'

/-! ## The reads, moved to the block's datum and to the pin's assignment -/

/-- `PinRead` mentions the datum's parameters only: it transfers from
the re-sorted datum to the block's. -/
theorem PinRead.of_sort {d : IndRepData V} {s : Level} {ψ : Name → Nat} {L : AnnotTerm}
    {DsA : List AnnotTerm} {n : Nat}
    (h : ({d with resSort := s} : IndRepData V).PinRead ψ L DsA n) : d.PinRead ψ L DsA n :=
  ⟨h.len, h.wd⟩

/-- `CopyIdxRead` from the re-sorted datum to the block's. -/
theorem CopyIdxRead.of_sort {d : IndRepData V} {s : Level}
    (hs : ∀ φ : Name → Nat, s.eval φ = d.resSort.eval φ) {ψ : Name → Nat} {t : Nat}
    {dJ : IndRepData V} {ψ' : Name → Nat} {mmJ : Nat} {DsA : List AnnotTerm}
    (h : ({d with resSort := s} : IndRepData V).CopyIdxRead ψ t dJ ψ' mmJ DsA) :
    d.CopyIdxRead ψ t dJ ψ' mmJ DsA :=
  ⟨by
    have h1 : dJ.w ψ' = s.eval ψ := h.sort
    show dJ.w ψ' = d.resSort.eval ψ
    rw [← hs ψ]; exact h1, h.nIdx, h.idxIff⟩

/-- `CopyIdxRead` at another assignment reading the container alike. -/
theorem CopyIdxRead.congr_assign {d : IndRepData V} {ψ : Name → Nat} {t : Nat}
    {dJ : IndRepData V} {ψ' ψ'' : Name → Nat} {mmJ : Nat} {DsA : List AnnotTerm}
    (hw : dJ.w ψ'' = dJ.w ψ') (hIds : dJ.IdsM mmJ ψ'' = dJ.IdsM mmJ ψ')
    (h : d.CopyIdxRead ψ t dJ ψ' mmJ DsA) : d.CopyIdxRead ψ t dJ ψ'' mmJ DsA :=
  ⟨hw.trans h.sort, h.nIdx, fun σ hσ is => by rw [hIds]; exact h.idxIff σ hσ is⟩

/-- A member's index telescope reads alike at two assignments agreeing
on the block's level parameters (`FormerData.params`). -/
theorem IdsM_congr {m : EnvModel V env} {cvT : ConstantVal} {dJ : IndRepData V} {t : Nat}
    (hFD : FormerData m cvT (dJ.nP + dJ.nIdxAt t) dJ.resSort (dJ.ppsM t) (dJ.lvlsM t))
    {ψ' ψ'' : Name → Nat} (hag : ∀ q ∈ cvT.levelParams, ψ'' q = ψ' q) :
    dJ.IdsM t ψ'' = dJ.IdsM t ψ' := by
  unfold IndRepData.IdsM
  rw [(hFD.params ψ'' ψ' hag).1]

/-! ## Every pin's facts, from the run -/

/-- The container member at a group position, and its pin. -/
theorem group_pin_eq {st : ElimState} {j₀ t : Nat} {q q' : NestedPin} {n n' : Name}
    {lvls lvls' : List Level} {Ds Ds' : List Expr}
    (hq : st.pins[j₀ + t]? = some q) (hq' : st.pins[j₀ + t]? = some q')
    (hp : q.pin = Expr.mkAppN (.const n lvls) Ds) (hp' : q'.pin = Expr.mkAppN (.const n' lvls') Ds') :
    n = n' ∧ lvls = lvls' ∧ Ds = Ds' := by
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  rw [hp] at hp'
  have h1 := congrArg Expr.getAppFn hp'
  rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at h1
  have h2 := congrArg Expr.getAppArgs hp'
  rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN] at h2
  simp only [Expr.getAppFn, Expr.getAppArgs, List.nil_append, Expr.const.injEq] at h1 h2
  exact ⟨h1.1, h1.2, h2⟩

/-- **What the run gives of one pin**, at a `CopyData` `c`: its
`PinFacts`, its position in its group, and the pin's own data — its
`NestedPin`, its container's block and member, its levels and
components, the group's pins, its stored former at the scratch
environment, its assignment, its readings — together with the
container's constructors as the datum's (`ContainerCtorsAt`) and the
copy's constructors from the mint to the store (`CopyCtorsStored`).
The per-pin body of `PinRunFacts`. -/
@[expose] def PinRunFactsAt {μ : CheckMode} (F : Nat) (env : Env) {envAux : Env} (p : ConLeche.NestedParts)
    (st : ElimState) (b : MutualBlock) (params : List Expr) (pbs : List (Expr × ConLeche.BinderMeta))
    (mpAux : EnvModelM V μ envAux) (d : IndRepData V) (ψ : Name → Nat) (c : CopyData V)
    (j : Nat) : Prop :=
  PinFacts mpAux d ψ p.k c ∧ c.base + c.mm = j ∧
  ∃ (q : NestedPin) (I : Name) (ci : ContainerInfo) (J : ContainerMember)
    (lvls : List Level) (Ds : List Expr) (cvTJ : ConstantVal) (capsJ : IndCaps),
    st.pins[j]? = some q ∧ ConLeche.containerInfo? env I = some ci ∧
    ci.members[c.mm]? = some J ∧ J.name = q.container ∧
    c.dJ.memberName c.mm = q.container ∧
    ci.members.length = c.dJ.k ∧
    (∀ i' J', ci.members[i']? = some J' →
      ∃ q', st.pins[c.base + i']? = some q' ∧ q'.container = J'.name ∧
        q'.pin = Expr.mkAppN (.const J'.name lvls) Ds ∧
        q'.grpBase = c.base ∧ q'.grpSize = ci.members.length) ∧
    q.pin = Expr.mkAppN (.const q.container lvls) Ds ∧
    ElimState.grp st j = (c.base, c.dJ.k) ∧
    envAux.find? q.container = some (.indInfo cvTJ capsJ) ∧
    c.ψ' = pinAssign c.dJ (Level.substFn ψ cvTJ.levelParams lvls) ∧
    -- the components' guards (K.3's `pinsClosed`): the readings are
    -- `bvarsBelow p.nP` (`DenoteMetaSpine.bvarsBelow`)
    (∀ a ∈ Ds, Expr.WScoped p.nP a ∧ a.looseBVarsBounded 0 = true) ∧
    DenoteMetaSpine mpAux.base2.acval envAux ψ p.nP Ds c.DsA ∧
    ContainerCtorsAt ci c.dJ ∧
    ConLeche.CopyCtorsStored μ F env p st b params pbs j J lvls Ds q ∧
    -- the group's members by name, and their leaves at the pin's
    -- assignment read as at the pin's level substitution (what a
    -- group-mate's own data agree with: `invChoice_group`, `InvCopy.lean`)
    ∀ (t : Nat) (J' : ContainerMember), ci.members[t]? = some J' →
      c.dJ.memberName t = J'.name ∧
      mpAux.base2.acval J'.name c.ψ'
        = mpAux.base2.acval J'.name (Level.substFn ψ J'.lps lvls)

/-- **What the run gives of one pin** (`PinRunFactsAt` at `cd j`),
together with the GROUP clause (task #279 M-C′, DESIGN §M.35): the
data of every group-mate `c.base + t` are the pin's own at member `t`
— ONE datum, assignment, readings and base per mint group, chosen at
the group's base pin — so that the fold's table entry at a group-mate
is literally the step at the pin's view of the group. -/
@[expose] def PinRunFacts {μ : CheckMode} (F : Nat) (env : Env) {envAux : Env} (p : ConLeche.NestedParts)
    (st : ElimState) (b : MutualBlock) (params : List Expr) (pbs : List (Expr × ConLeche.BinderMeta))
    (mpAux : EnvModelM V μ envAux) (d : IndRepData V) (ψ : Name → Nat) (cd : Nat → CopyData V)
    (j : Nat) : Prop :=
  PinRunFactsAt F env p st b params pbs mpAux d ψ (cd j) j ∧
  ∀ t, t < (cd j).dJ.k →
    cd ((cd j).base + t) = ⟨(cd j).dJ, t, (cd j).ψ', (cd j).DsA, (cd j).base⟩

set_option maxHeartbeats 1600000 in
/-- **Every pin has its group facts, from the run** — one `CopyData` per
pin (`cd`), its container the datum `ContainersRep` gives for the pin's
group, its member the ledger's position in the group, its assignment
`pinAssign` at the pin's levels, its readings the pin's inference's
(`DenoteMetaSpine`, the same list for a whole group), its base the
group's; with the pin's own data exposed for the constructor side and
the bridge.  The datum, assignment and readings are chosen ONCE per
mint group (at the group's base pin, `ElimState.grp`), so the
group-mates' data are the pin's own (`PinRunFacts`' group clause). -/
theorem pinFacts_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env) (params : List Expr)
      (pbs : List (Expr × ConLeche.BinderMeta)) (fmsA ctorsA : List ConstantVal) (order : List Nat),
      ConLeche.auxBlock p st = some b ∧
      ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st ∧
      ConLeche.nestedTopoOrder (ElimState.grp st) p.k st = .ok order ∧
      st.types.length = p.k + st.pins.length ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
        CtorsChecked μ F env b true d ∧
        (ContainersRep env envAux mpAux.base2 → ∀ ψ : Name → Nat,
          ∃ cd : Nat → CopyData V, ∀ j, j < st.pins.length →
            PinRunFacts F env p st b params pbs mpAux d ψ cd j) := by
  obtain ⟨st, b, envAux, params, pbs, fmsA, ctorsA, order, hb, helim, hord, hlenSt, -, mpAux, d,
    hreps, hchk, hpins⟩ := copyIdxRead_of_run hμ mp hE h
  refine ⟨st, b, envAux, params, pbs, fmsA, ctorsA, order, hb, helim, hord, hlenSt, mpAux, d, hreps,
    hchk, ?_⟩
  intro hcr ψ
  obtain ⟨-, hkb, -, -, -, -, -, -⟩ := hreps
  have hdk : d.k = p.k + st.pins.length := by rw [hkb, ConLeche.auxBlock_k hb, hlenSt]
  -- a pin's group base is a base: its group's first pin carries it
  have hbaseOf : ∀ j, j < st.pins.length →
      (ElimState.grp st j).1 < st.pins.length ∧
      ElimState.grp st (ElimState.grp st j).1 = ElimState.grp st j := by
    intro j hj
    obtain ⟨q, I, ci, i, j₀, J, lvls, Ds, hq, hci, hJ, hjE, hgrp, -, -, hqb, hqs, -, -, -, -⟩ :=
      hpins j hj
    have hg : ElimState.grp st j = (j₀, ci.members.length) := by
      unfold ElimState.grp; rw [hq]; show (q.grpBase, q.grpSize) = _; rw [hqb, hqs]
    obtain ⟨J₀, hJ₀⟩ : ∃ J₀, ci.members[0]? = some J₀ :=
      ⟨_, List.getElem?_eq_getElem (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.getElem?_eq_some_iff.mp hJ).1)⟩
    obtain ⟨q₀, hq₀, -, -, hq₀b, hq₀s⟩ := hgrp 0 J₀ hJ₀
    rw [Nat.add_zero] at hq₀
    rw [hg]
    refine ⟨(List.getElem?_eq_some_iff.mp hq₀).1, ?_⟩
    show ElimState.grp st j₀ = (j₀, ci.members.length)
    unfold ElimState.grp; rw [hq₀]; show (q₀.grpBase, q₀.grpSize) = _; rw [hq₀b, hq₀s]
  -- one GROUP, at its base pin `j₀`: one datum, assignment and readings
  -- for every member
  have hone : ∀ j₀, j₀ < st.pins.length → (ElimState.grp st j₀).1 = j₀ →
      ∃ (dJ : IndRepData V) (ψ' : Name → Nat) (DsA : List AnnotTerm),
        (ElimState.grp st j₀).2 = dJ.k ∧
        ∀ t, t < dJ.k →
          PinRunFactsAt F env p st b params pbs mpAux d ψ ⟨dJ, t, ψ', DsA, j₀⟩ (j₀ + t) := by
    intro j₀ hj₀ hg₀
    obtain ⟨q, I, ci, i, j₀', J, lvls, Ds, hq, hci, hJ, hjE, hgrp, hqc, hqp, hqb, hqs, hDsLen, -,
      -, hread⟩ := hpins j₀ hj₀
    -- the pin IS its group's base: member `0`
    have hg : ElimState.grp st j₀ = (j₀', ci.members.length) := by
      unfold ElimState.grp; rw [hq]; show (q.grpBase, q.grpSize) = _; rw [hqb, hqs]
    have hj₀' : j₀ = j₀' := by
      rw [hg] at hg₀; exact hg₀.symm
    subst hj₀'
    have hi0 : i = 0 := by omega
    subst hi0
    obtain ⟨dJ, hctorsC, hkR, hciNP, hlenM, hpinsAV, hview, hprop, hcat, hmem⟩ := hcr I ci hci
    obtain ⟨cvTJ, cvR, capsJ, mI, rP, rules, hfJ, hJty, hJlps, hrules, hfR, hfresh, hrep⟩ :=
      hmem 0 J hJ
    have hik : 0 < dJ.k := by rw [← hlenM]; exact (List.getElem?_eq_some_iff.mp hJ).1
    have hFDJ : FormerData mpAux.base2 cvTJ (dJ.nP + dJ.nIdxAt 0) dJ.resSort (dJ.ppsM 0)
        (dJ.lvlsM 0) :=
      hrep.formersRead 0 (by rw [hkR]; exact hik) cvTJ capsJ (by rw [hrep.member]; exact hfJ)
    obtain ⟨s, DsA, hsv, hargs, hsp, hpin, hidx⟩ := hread ψ cvTJ capsJ dJ 0 hfJ hJty hJlps hciNP hFDJ
    -- the assignment
    obtain ⟨ψ'₀, hψ'₀⟩ : ∃ x, x = Level.substFn ψ cvTJ.levelParams lvls := ⟨_, rfl⟩
    obtain ⟨ψ', hψ'⟩ : ∃ x, x = pinAssign dJ ψ'₀ := ⟨_, rfl⟩
    have hagree : ∀ q ∈ cvTJ.levelParams, ψ' q = ψ'₀ q := by
      rw [hψ']; exact pinAssign_agree hfresh
    have hw : dJ.w ψ' = dJ.w ψ'₀ := (hFDJ.params ψ' ψ'₀ hagree).2
    have hlev : dJ.elimL.eval ψ' = dJ.w ψ' := by subst hψ'; exact pinAssign_lev hw hprop
    have hlenD : DsA.length = dJ.nP := by rw [hpin.len, hDsLen, hciNP]
    -- the group's pins exist
    have hposGrp : ∀ t, t < dJ.k → j₀ + t < st.pins.length := by
      intro t ht
      obtain ⟨J', hJ'⟩ : ∃ J', ci.members[t]? = some J' :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlenM]; exact ht)⟩
      obtain ⟨q', hq', -, -, -, -⟩ := hgrp t J' hJ'
      exact (List.getElem?_eq_some_iff.mp hq').1
    -- every group-mate's stored former has the block's level parameters
    have hlpsOf : ∀ t, t < dJ.k → ∀ (cv : ConstantVal) (caps : IndCaps),
        envAux.find? (dJ.memberName t) = some (.indInfo cv caps) → cv.levelParams = cvTJ.levelParams :=
      fun t ht cv caps hf => hrep.membersLps t ht cv caps hf
    -- every group-mate's data are live
    have hgrpOk : ∀ t, t < dJ.k →
        CopyData.Ok mpAux.base2 d ψ p.k (j₀ + t) ⟨dJ, t, ψ', DsA, j₀⟩ := by
      intro t ht
      obtain ⟨J', hJ'⟩ : ∃ J', ci.members[t]? = some J' :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlenM]; exact ht)⟩
      obtain ⟨q', hq', hq'c, hq'p, -, -⟩ := hgrp t J' hJ'
      obtain ⟨cvTJ', cvR', capsJ', mI', rP', rules', hfJ', hJty', hJlps', -, -, -, hrep'⟩ :=
        hmem t J' hJ'
      have hfJ'' : envAux.find? (dJ.memberName t) = some (.indInfo cvTJ' capsJ') := by
        rw [hrep'.member]; exact hfJ'
      have hlpsT : cvTJ'.levelParams = cvTJ.levelParams := hlpsOf t ht cvTJ' capsJ' hfJ''
      have hFDJ' : FormerData mpAux.base2 cvTJ' (dJ.nP + dJ.nIdxAt t) dJ.resSort (dJ.ppsM t)
          (dJ.lvlsM t) :=
        hrep'.formersRead t (by rw [hkR]; exact ht) cvTJ' capsJ' hfJ''
      -- the read at the group-mate's pin, at this datum
      obtain ⟨qt, It, cit, it, j₀t, Jt, lvlst, Dst, hqt, hcit, hJt, -, -, hqtc, hqtp, -, -, hDsLent,
        -, -, hreadt⟩ := hpins (j₀ + t) (hposGrp t ht)
      obtain ⟨hJtn, hlv, hDsE⟩ := group_pin_eq hqt hq' hqtp hq'p
      rw [hlv, hDsE] at hreadt
      rw [hDsE] at hDsLent
      -- the same stored constant, so the same type and level parameters
      obtain ⟨⟨cvC, capsC, hfC, htyC, hlpsC⟩, -⟩ := ConLeche.containerInfo?_stored hcit Jt
        (List.mem_of_getElem? hJt)
      obtain ⟨⟨cvC', capsC', hfC', htyC', hlpsC'⟩, -⟩ := ConLeche.containerInfo?_stored hci J'
        (List.mem_of_getElem? hJ')
      rw [hJtn] at hfC
      obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfC.symm.trans hfC'))
      have hJtty : Jt.type = cvTJ'.type := by rw [htyC, ← htyC', hJty']
      have hJtlps : Jt.lps = cvTJ'.levelParams := by rw [hlpsC, ← hlpsC', hJlps']
      have hcitNP : cit.nP = dJ.nP := by rw [← hDsLent, hDsLen, hciNP]
      obtain ⟨st', DsA', hsv', -, hsp', hpin', hidx'⟩ :=
        hreadt ψ cvTJ' capsJ' dJ t (by rw [hJtn]; exact hfJ') hJtty hJtlps hcitNP hFDJ'
      obtain rfl : DsA = DsA' := denoteMetaSpine_eq hsp hsp'
      -- the assignment agrees on the container's level parameters
      have hagree' : ∀ q ∈ cvTJ'.levelParams, ψ' q = Level.substFn ψ cvTJ'.levelParams lvls q := by
        rw [hlpsT, ← hψ'₀]; exact hagree
      have hacv : mpAux.base2.acval Jt.name ψ'
          = mpAux.base2.acval Jt.name (Level.substFn ψ cvTJ'.levelParams lvls) :=
        mpAux.base2.acval_params Jt.name (.indInfo cvTJ' capsJ') (by rw [hJtn]; exact hfJ') _ _
          hagree'
      refine ⟨by show p.k + j₀ + t = p.k + (j₀ + t); omega, ht, hlenD,
        IndRepData.formerFacts_of_indRep dJ hrep' hkR ψ' ht,
        hrep'.leafShape t (by rw [hkR]; exact ht) ψ',
        hpinsAV t, hrep'.paramsIffM t (by rw [hkR]; exact ht) ψ', ?_, ?_⟩
      · show d.PinRead ψ (mpAux.base2.acval (dJ.memberName t) ψ') DsA dJ.nP
        rw [hrep'.member, ← hJtn, hacv]
        have hpin'' := PinRead.of_sort hpin'
        rw [hDsLen, hciNP] at hpin''
        exact hpin''
      · show d.CopyIdxRead ψ (p.k + (j₀ + t)) dJ ψ' t DsA
        refine CopyIdxRead.congr_assign ?_ (IdsM_congr hFDJ' hagree') (CopyIdxRead.of_sort hsv' hidx')
        exact (hFDJ'.params ψ' _ hagree').2
    -- the group's members by name, and their leaves
    have hab : ∀ (t : Nat) (J' : ContainerMember), ci.members[t]? = some J' →
        dJ.memberName t = J'.name ∧
        mpAux.base2.acval J'.name ψ' = mpAux.base2.acval J'.name (Level.substFn ψ J'.lps lvls) := by
      intro t J' hJ'
      have ht : t < dJ.k := by rw [← hlenM]; exact (List.getElem?_eq_some_iff.mp hJ').1
      obtain ⟨cvTJ', cvR', capsJ', mI', rP', rules', hfJ', -, hJlps', -, -, -, hrep'⟩ :=
        hmem t J' hJ'
      have hfJ'' : envAux.find? (dJ.memberName t) = some (.indInfo cvTJ' capsJ') := by
        rw [hrep'.member]; exact hfJ'
      have hlpsT : cvTJ'.levelParams = cvTJ.levelParams := hlpsOf t ht cvTJ' capsJ' hfJ''
      refine ⟨hrep'.member, ?_⟩
      refine mpAux.base2.acval_params J'.name (.indInfo cvTJ' capsJ') hfJ' _ _ ?_
      intro q hq
      have hq' : q ∈ cvTJ.levelParams := by rw [← hlpsT]; exact hq
      show ψ' q = Level.substFn ψ J'.lps lvls q
      rw [hJlps', hlpsT, ← hψ'₀]
      exact hagree q hq'
    refine ⟨dJ, ψ', DsA, by rw [hg, hlenM], fun t ht => ?_⟩
    -- member `t`'s own pin
    obtain ⟨Jt, hJt⟩ : ∃ Jt, ci.members[t]? = some Jt :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenM]; exact ht)⟩
    obtain ⟨qt, hqt, hqtc, hqtp, hqtb, hqts⟩ := hgrp t Jt hJt
    obtain ⟨cvTJt, cvRt, capsJt, mIt, rPt, rulest, hfJt, -, hJlpst, -, -, -, hrept⟩ := hmem t Jt hJt
    have hfJt' : envAux.find? (dJ.memberName t) = some (.indInfo cvTJt capsJt) := by
      rw [hrept.member]; exact hfJt
    have hlpst : cvTJt.levelParams = cvTJ.levelParams := hlpsOf t ht cvTJt capsJt hfJt'
    -- its stored constructors, from its own run facts
    obtain ⟨qt', It', cit', it', j₀t', Jt', lvlst', Dst', hqt', hcit', hJt', -, -, hqtc', hqtp', -, -,
      -, -, hcstt, -⟩ := hpins (j₀ + t) (hposGrp t ht)
    obtain ⟨hJtn', hlv', hDsE'⟩ := group_pin_eq hqt' hqt hqtp' hqtp
    obtain rfl : qt = qt' := Option.some.inj (hqt.symm.trans hqt')
    have hJtE : Jt = Jt' :=
      (ConLeche.containerInfo?_member_eq hcit' hci (List.mem_of_getElem? hJt') (List.mem_of_getElem? hJt)
        hJtn').symm
    subst hJtE
    rw [hlv', hDsE'] at hcstt
    refine ⟨⟨ht, hctorsC, hkR, hpinsAV, hview,
        ⟨J.name, cvTJ, cvR, mI, rP, rules, 0, hik, hrules, hfR, hrep⟩, ?_, hlenD, hlev,
        fun t' ht' => by show p.k + j₀ + t' < d.k; have := hposGrp t' ht'; omega, hgrpOk⟩,
      rfl,
      qt, I, ci, Jt, lvls, Ds, cvTJt, capsJt, hqt, hci, hJt, hqtc.symm, by rw [hrept.member, hqtc],
      hlenM, hgrp, by rw [hqtp, hqtc], ?_, by rw [hqtc]; exact hfJt, by rw [hψ', hψ'₀, hlpst], hargs,
      hsp, hcat, hcstt, hab⟩
    · intro t' ht'
      obtain ⟨J', hJ'⟩ : ∃ J', ci.members[t']? = some J' :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlenM]; exact ht')⟩
      obtain ⟨cvTJ', cvR', capsJ', mI', rP', rules', -, -, -, -, -, -, hrep'⟩ := hmem t' J' hJ'
      refine ⟨cvTJ', cvR', mI', rP', rules', ?_⟩
      rw [hrep'.member]
      exact hrep'
    show ElimState.grp st (j₀ + t) = (j₀, dJ.k)
    unfold ElimState.grp
    rw [hqt]
    show (qt.grpBase, qt.grpSize) = (j₀, dJ.k)
    rw [hqtb, hqts, hlenM]
  -- the choice, per GROUP: one datum, assignment and readings per base pin
  have hchoice : ∃ (dOf : Nat → IndRepData V) (ψOf : Nat → Name → Nat) (DsOf : Nat → List AnnotTerm),
      ∀ j₀, j₀ < st.pins.length → (ElimState.grp st j₀).1 = j₀ →
        (ElimState.grp st j₀).2 = (dOf j₀).k ∧
        ∀ t, t < (dOf j₀).k →
          PinRunFactsAt F env p st b params pbs mpAux d ψ ⟨dOf j₀, t, ψOf j₀, DsOf j₀, j₀⟩ (j₀ + t) := by
    refine ⟨fun j₀ => if h : j₀ < st.pins.length ∧ (ElimState.grp st j₀).1 = j₀ then
        Classical.choose (hone j₀ h.1 h.2) else d,
      fun j₀ => if h : j₀ < st.pins.length ∧ (ElimState.grp st j₀).1 = j₀ then
        Classical.choose (Classical.choose_spec (hone j₀ h.1 h.2)) else ψ,
      fun j₀ => if h : j₀ < st.pins.length ∧ (ElimState.grp st j₀).1 = j₀ then
        Classical.choose (Classical.choose_spec (Classical.choose_spec (hone j₀ h.1 h.2))) else [],
      ?_⟩
    intro j₀ hj₀ hg₀
    simp only
    rw [dif_pos (And.intro hj₀ hg₀), dif_pos (And.intro hj₀ hg₀), dif_pos (And.intro hj₀ hg₀)]
    exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hone j₀ hj₀ hg₀)))
  obtain ⟨dOf, ψOf, DsOf, hOf⟩ := hchoice
  -- a pin's data are its base's at its position
  refine ⟨fun j => ⟨dOf (ElimState.grp st j).1, j - (ElimState.grp st j).1, ψOf (ElimState.grp st j).1,
    DsOf (ElimState.grp st j).1, (ElimState.grp st j).1⟩, fun j hj => ?_⟩
  obtain ⟨hb₁, hb₂'⟩ := hbaseOf j hj
  have hb₂ : (ElimState.grp st (ElimState.grp st j).1).1 = (ElimState.grp st j).1 := by rw [hb₂']
  obtain ⟨hsz, hall⟩ := hOf _ hb₁ hb₂
  -- the pin's position in its group
  obtain ⟨q, I, ci, i, j₀, J, lvls, Ds, hq, hci, hJ, hjE, hgrp, -, -, hqb, hqs, -, -, -, -⟩ :=
    hpins j hj
  have hg : ElimState.grp st j = (j₀, ci.members.length) := by
    unfold ElimState.grp; rw [hq]; show (q.grpBase, q.grpSize) = _; rw [hqb, hqs]
  have hi : i < ci.members.length := (List.getElem?_eq_some_iff.mp hJ).1
  have hsub : j - (ElimState.grp st j).1 = i := by rw [hg]; show j - j₀ = i; omega
  have hlt : i < (dOf (ElimState.grp st j).1).k := by
    rw [← hsz, hb₂', hg]; exact hi
  have hjE' : j = (ElimState.grp st j).1 + i := by rw [hg]; exact hjE
  unfold PinRunFacts
  refine ⟨?_, ?_⟩
  · simp only
    rw [hsub]
    have h := hall i hlt
    rw [← hjE'] at h
    exact h
  · intro t ht
    simp only at ht ⊢
    -- the group-mate's base is the same pin
    have hm := hall t ht
    obtain ⟨-, -, q', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg', -⟩ := hm
    have hE : (ElimState.grp st ((ElimState.grp st j).1 + t)).1 = (ElimState.grp st j).1 := by
      rw [hg']
    rw [hE]
    simp only [Nat.add_sub_cancel_left]

/-! ## The auxiliary datum's own facts, from the block's representations -/

/-- **The scratch block's real-member facts at its datum**: every member
is a real member (`MutualBlockReps`), so its former facts, leaf shape
and parameter equivalence hold at the block's datum — read off the
member's representation at its re-sorted datum and moved to the
block's sort (`congr_sort`; the two evaluate alike). -/
theorem auxFacts_of_blockReps {μ : CheckMode} {mpAux : EnvModelM V μ env} {b : MutualBlock}
    {d : IndRepData V} (hreps : MutualBlockReps mpAux.base2 b d) (ψ : Name → Nat) :
    (∀ t, d.pinsOf ψ t = paramBvarsAt d.nP d.nP) ∧
    (∀ t, t < d.k → d.FormerFacts mpAux.base2 ψ t) ∧
    (∀ t, t < d.k → d.LeafShape mpAux.base2 ψ t) ∧
    (∀ t, t < d.k → ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ') := by
  obtain ⟨-, hkb, hkRb, -, hpinsAV, -, -, hall⟩ := hreps
  refine ⟨fun t => hpinsAV t ψ, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨s, cvT, cvR, caps, mI, rP, rules, -, -, -, hsv, hrep⟩ := hall t (by rw [← hkb]; exact ht)
    have hkR : ({d with resSort := s} : IndRepData V).kReal
        = ({d with resSort := s} : IndRepData V).k := by
      show d.kReal = d.k
      rw [hkb, hkRb]
    have h := IndRepData.formerFacts_of_indRep ({d with resSort := s} : IndRepData V) hrep hkR ψ
      (t := t) ht
    exact FormerFacts.congr_sort (d := d) (s' := d.resSort) hsv h
  · obtain ⟨s, cvT, cvR, caps, mI, rP, rules, -, -, -, hsv, hrep⟩ := hall t (by rw [← hkb]; exact ht)
    have h := hrep.leafShape t (by show t < d.kReal; rw [hkRb, ← hkb]; exact ht) ψ
    exact LeafShape.congr_sort (d := d) (s' := d.resSort) hsv h
  · obtain ⟨s, cvT, cvR, caps, mI, rP, rules, -, -, -, -, hrep⟩ := hall t (by rw [← hkb]; exact ht)
    exact hrep.paramsIffM t (by show t < d.kReal; rw [hkRb, ← hkb]; exact ht) ψ

/-! ## ψ at every pin, from the run -/

/-- **The constructor-side premise**: at every pin, the container's
constructors are matched by the copy's (`auxOfs j`) with the facts
`psiSetup_of_group` consumes (`CopyCtorFacts`: the record
`CopyCtorAsRead`, the copy's constructor facts in the auxiliary datum,
its closedness, parameter equivalence, view identities, targets and
member) — what `nestedCopyCtorType_eq`'s identity arm reads
(DESIGN §M.26) and the whnf arm owes. -/
@[expose] def CopyCtorsOfRun {μ : CheckMode} (mp : EnvModelM V μ env) (d : IndRepData V) (ψ : Name → Nat)
    (k₀ n : Nat) (lpsT : List Name) (cd : Nat → CopyData V) (auxOfs : Nat → Nat → Nat) : Prop :=
  ∀ j', j' < n → ∀ Jc cAJ, (cd j').dJ.ctorsA[Jc]? = some cAJ →
    ∃ cAa, d.ctorsA[auxOfs j' Jc]? = some cAa ∧
      CopyCtorFacts mp.base2 d (cd j').dJ ψ (cd j').ψ' (cd j').DsA k₀ (cd j').base cd lpsT Jc
        (auxOfs j' Jc) cAJ cAa

/-- **The bridge**: every transport's target — a field the copy's
constructor sees as recursive and the container's as ordinary — is a
reference of the kernel's relation (`CopyRef`: mentioned, outside the
group, no group pin inside its pin). -/
@[expose] def BridgeOfRun (d : IndRepData V) (st : ElimState) (k₀ n : Nat) (cd : Nat → CopyData V)
    (auxOfs : Nat → Nat → Nat) : Prop :=
  ∀ j', j' < n → ∀ Jc cAJ, (cd j').dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
    i ∈ ConLeche.recIdxOf (d.ksR (auxOfs j' Jc)) → i ∉ ConLeche.recIdxOf ((cd j').dJ.ksF Jc) →
    k₀ ≤ d.tgtsR (auxOfs j' Jc) i →
    ConLeche.CopyRef (ElimState.grp st) k₀ st j' (d.tgtsR (auxOfs j' Jc) i - k₀)

/-- **The bridge's SYNTACTIC half**: at every transport — a field the
copy's constructor sees as recursive into pin `j''`'s copy and the
container's as ordinary — SOME copy of the source's mint group has a
processed constructor MENTIONING the target copy's name (the group-wide
form of `CopyRef`'s mention clause, K.15: ψ at a pin folds the whole
group's constructors), and no pin of the source's group is a sub-term
of the target's pin.  What the run owes of the elimination's output
(DESIGN §M.28): the mention from the walk's rewrite at the field
(`replaceIfNested_some`) through the normalisation, the sub-term clause
from the container's positivity (an ordinary field mentions no member
of the container's group). -/
@[expose] def BridgeSyntax (d : IndRepData V) (st : ElimState) (k₀ n : Nat) (cd : Nat → CopyData V)
    (auxOfs : Nat → Nat → Nat) : Prop :=
  ∀ j', j' < n → ∀ Jc cAJ, (cd j').dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
    i ∈ ConLeche.recIdxOf (d.ksR (auxOfs j' Jc)) → i ∉ ConLeche.recIdxOf ((cd j').dJ.ksF Jc) →
    k₀ ≤ d.tgtsR (auxOfs j' Jc) i →
    ∀ (t' : AuxType) (q' : NestedPin),
      st.types[d.tgtsR (auxOfs j' Jc) i]? = some t' →
      st.pins[d.tgtsR (auxOfs j' Jc) i - k₀]? = some q' →
      (∃ g, g < (cd j').dJ.k ∧ ∃ tg : AuxType, st.types[k₀ + (cd j').base + g]? = some tg ∧
        ∃ c ∈ tg.ctors, (c.2.1).mentionsConst t'.name = true) ∧
      ∀ (l : Nat) (g : NestedPin), l < (cd j').dJ.k → st.pins[(cd j').base + l]? = some g →
        ¬ Expr.Sub g.pin q'.pin

/-- **The bridge, from its syntactic half**: the target's position and
its exclusion from the source's group are the record's `kindT`
(`CopyCtorFacts.read`), the target is a pin (`CopyCtorFacts.tgts` at
the block's size), and the source's group is the pin's own
(`ElimState.grp`). -/
theorem bridgeOfRun_of_syntax {μ : CheckMode} {mp : EnvModelM V μ env} {d : IndRepData V}
    {ψ : Name → Nat} {st : ElimState} {k₀ n : Nat} {lpsT : List Name} {cd : Nat → CopyData V}
    {auxOfs : Nat → Nat → Nat} (hn : st.pins.length = n) (hlenSt : st.types.length = k₀ + n)
    (hkn : d.k ≤ k₀ + n)
    (hgrp : ∀ j, j < n → ElimState.grp st j = ((cd j).base, (cd j).dJ.k))
    (hctors : CopyCtorsOfRun mp d ψ k₀ n lpsT cd auxOfs)
    (hsyn : BridgeSyntax d st k₀ n cd auxOfs) : BridgeOfRun d st k₀ n cd auxOfs := by
  intro j' hj' Jc cAJ hJc i hi hA hT hk
  obtain ⟨cAa, -, hf⟩ := hctors j' hj' Jc cAJ hJc
  obtain ⟨j'', hj'', hout, -, -⟩ := hf.read.kindT i hi hT hA hk
  have htgt : d.tgtsR (auxOfs j' Jc) i < d.k := hf.tgts i
  have hj''n : d.tgtsR (auxOfs j' Jc) i - k₀ < n := by omega
  have hjE : d.tgtsR (auxOfs j' Jc) i - k₀ = j'' := by omega
  obtain ⟨t, ht⟩ : ∃ t, st.types[k₀ + j']? = some t :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenSt]; omega)⟩
  obtain ⟨t', ht'⟩ : ∃ t', st.types[k₀ + (d.tgtsR (auxOfs j' Jc) i - k₀)]? = some t' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenSt]; omega)⟩
  obtain ⟨q', hq'⟩ : ∃ q', st.pins[d.tgtsR (auxOfs j' Jc) i - k₀]? = some q' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hn]; exact hj''n)⟩
  have ht'' : st.types[d.tgtsR (auxOfs j' Jc) i]? = some t' := by
    rw [show d.tgtsR (auxOfs j' Jc) i = k₀ + (d.tgtsR (auxOfs j' Jc) i - k₀) by omega]
    exact ht'
  obtain ⟨hmention, hsub⟩ := hsyn j' hj' Jc cAJ hJc i hi hA hT hk t' q' ht'' hq'
  refine ⟨t, t', q', ht, ht', hq', ?_, ?_, ?_⟩
  · rw [hgrp j' hj']
    exact hmention
  · rw [hgrp j' hj', hjE]
    exact hout
  · intro l g hl hg
    rw [hgrp j' hj'] at hl hg
    exact hsub l g hl hg

set_option maxHeartbeats 800000 in
/-- **ψ AT EVERY PIN, FROM THE RUN** (task #279 M-B′, DESIGN §M.28):
under the containers' representation (`ContainersRep`), for every
level assignment and parameter frame of the scratch block, the fold of
the copies' terms along the KERNEL's order (`nestedTopoOrder`, read as
`TopoOrder (CopyRef …)` by `topoOrder_of_run`) is `PsiTypedPi` at every
pin — given the constructor side (`CopyCtorsOfRun`) and the bridge
(`BridgeOfRun`) at the pins' data `cd` this run reads
(`pinFacts_of_run`). -/
theorem psiFold_typed_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env) (order : List Nat),
      ConLeche.auxBlock p st = some b ∧
      ConLeche.nestedTopoOrder (ElimState.grp st) p.k st = .ok order ∧
      st.types.length = p.k + st.pins.length ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
        CtorsChecked μ F env b true d ∧
        ∃ (params : List Expr) (pbs : List (Expr × ConLeche.BinderMeta)),
        (ContainersRep env envAux mpAux.base2 → ∀ ψ : Name → Nat,
          ∃ cd : Nat → CopyData V,
            (∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j) ∧
            ∀ (lpsT : List Name) (auxOfs : Nat → Nat → Nat),
              CopyCtorsOfRun mpAux d ψ p.k st.pins.length lpsT cd auxOfs →
              BridgeSyntax d st p.k st.pins.length cd auxOfs →
              ∀ (ρ₀ : Nat → V) (psA : List AnnotTerm), psA.length = d.nP →
                SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀)) →
                ∀ (tbl₀ : Nat → AnnotTerm) (j' : Nat), j' < st.pins.length →
                  d.PsiP mpAux.base2 ψ p.k (consList (psA.map (interp V ρ₀)) ρ₀) cd j'
                    (ConLeche.orderFold (d.psiStep mpAux.base2 ψ p.k cd auxOfs) order tbl₀ j')) := by
  obtain ⟨st, b, envAux, params, pbs, fmsA, ctorsA, order, hb, -, hord, hlenSt, mpAux, d, hreps,
    hchk, hpins⟩ := pinFacts_of_run hμ mp hE h
  refine ⟨st, b, envAux, order, hb, hord, hlenSt, mpAux, d, hreps, hchk, params, pbs, ?_⟩
  intro hcr ψ
  obtain ⟨cd, hcd⟩ := hpins hcr ψ
  have hgrp : ∀ j, j < st.pins.length → ElimState.grp st j = ((cd j).base, (cd j).dJ.k) := by
    intro j hj
    obtain ⟨⟨-, -, q, I, ci, J, lvls, Ds, cvTJ, capsJ, -, -, -, -, -, -, -, -, hg, -⟩, -⟩ := hcd j hj
    exact hg
  refine ⟨cd, hcd, ?_⟩
  intro lpsT auxOfs hctors hsyn ρ₀ psA hpsA hparamsA tbl₀ j' hj'
  obtain ⟨hpinsA, hFFA, hLSA, hpIffMA⟩ := auxFacts_of_blockReps hreps ψ
  obtain ⟨-, hkb, -, -, -, -, -, -⟩ := hreps
  have hkn : d.k ≤ p.k + st.pins.length := by
    rw [hkb, ConLeche.auxBlock_k hb, hlenSt]
    exact Nat.le_refl _
  have hbridge : BridgeOfRun d st p.k st.pins.length cd auxOfs :=
    bridgeOfRun_of_syntax rfl hlenSt hkn hgrp hctors hsyn
  have hall : ∀ j, j < st.pins.length →
      GroupFacts mpAux d ψ p.k lpsT cd (cd j) (auxOfs j) ∧ (cd j).base + (cd j).mm = j := by
    intro j hj
    exact ⟨GroupFacts.of_pinFacts (hcd j hj).1.1 (hctors j hj), (hcd j hj).1.2.1⟩
  exact d.psiFold_typed mpAux hpsA hparamsA hpinsA hFFA hLSA hpIffMA hkn hall hbridge
    (ConLeche.topoOrder_of_run hlenSt hord) tbl₀ j' hj'

end ConLeche.Model
