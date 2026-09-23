module

public import ConLeche.Model.Inductives.DeclNative
public import ConLeche.Model.Inductives.BlockDatum
public import ConLeche.Semantics.Inductives.DeclBlock
import ConLeche.Verify.Inductives.BlockPartsInv
public section

/-!
# The uniform block install, assembled (task #315 M3)

`declBlock`: **the P carrier survives the UNIFORM install's run at `k`
members.**  This is the Model tier's half of the milestone-M1 flip
stated over the uniform installer itself (`checkBlock`) — the shape
`Model/Fold.lean`'s dispatch will take once the route is ungated.

`declBlock` covers `k = 1` like every other width; the fold reaches it
through `declBlock_run` (`Model/Inductives/BlockDeclRun.lean`).

**What is NOT here**: `declBlock` for all `k`, and the named fact
`BlockRecStaged` its recursor stage would carry.  Both wait on the
stage theorems (the k-former loop, the constructors' loop over
members, the tables per structure-like member); writing the named fact
before its stage shapes are fixed would be a hypothesis without a
run-level consumer.  What exists of the stage chain today is listed in
`_tmp/uniform-inds/M3-REPORT.md` §3.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BlockShape BlockParts MemberShape BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## `NoProjEnv` across the block's conses -/

/-- The `k` formers' cons keeps a member's slots free: a former's type
resolves before the block, and an `indInfo` carries nothing else. -/
theorem noProjEnv_consBlockInds {T : Name} {i : Nat} {p₁ : ConLeche.BlockShape} {isRec : Bool} :
    ∀ {cvTas : List ConstantVal} {j : Nat} {env₀ : Env},
      NoProjEnv env₀ T i → (∀ cvTa ∈ cvTas, Expr.NoProjAt T i cvTa.type) →
      NoProjEnv (ConLeche.consBlockInds p₁ isRec cvTas j env₀) T i
  | [], _, _, h, _ => h
  | cvTa :: rest, j, env₀, h, hall => by
    simp only [ConLeche.consBlockInds]
    refine noProjEnv_consBlockInds
      (h.cons (c₀ := .indInfo cvTa (ConLeche.blockCapsAt p₁ j isRec)) (NoProjHead.ofType
        (hall cvTa List.mem_cons_self) (fun _ _ _ h => nomatch h)
        (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h))) ?_
    exact fun c hc => hall c (List.mem_cons_of_mem _ hc)

/-- The members' constructors' conses keep a member's slots free. -/
theorem noProjEnv_consBlockCtors {T : Name} {i nP : Nat} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env₀ : Env},
      NoProjEnv env₀ T i →
      (∀ ctorsA ∈ ctorsAs, ∀ cA ∈ ctorsA, Expr.NoProjAt T i cA.1.type) →
      NoProjEnv (ConLeche.consBlockCtors nP ctorsAs env₀) T i
  | [], _, h, _ => h
  | ctorsA :: rest, env₀, h, hall => by
    simp only [ConLeche.consBlockCtors]
    refine noProjEnv_consBlockCtors
      (noProjEnv_consSumCtors h (hall ctorsA List.mem_cons_self)) ?_
    exact fun l hl => hall l (List.mem_cons_of_mem _ hl)

/-- A name absent above the `k` formers' cons was absent below it. -/
theorem find?_none_consBlockInds {p₁ : ConLeche.BlockShape} {isRec : Bool} {n : Name} :
    ∀ {cvTas : List ConstantVal} {j : Nat} {env₀ : Env},
      (ConLeche.consBlockInds p₁ isRec cvTas j env₀).find? n = none → env₀.find? n = none
  | [], _, _, h => h
  | _ :: rest, j, _env₀, h =>
    find?_none_of_consB (find?_none_consBlockInds (cvTas := rest) (j := j + 1) h)

/-- A name absent above the constructors' conses was absent below them. -/
theorem find?_none_consBlockCtors {nP : Nat} {n : Name} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env₀ : Env},
      (ConLeche.consBlockCtors nP ctorsAs env₀).find? n = none → env₀.find? n = none
  | [], _, h => h
  | _ :: rest, _env₀, h =>
    ConLeche.consSumCtors_find?_none (find?_none_consBlockCtors (ctorsAs := rest) h)

/-- A name absent above the recursors' conses was absent below them. -/
theorem find?_none_consBlockRecs {find? : Name → Option ConstantInfo} {q : ConLeche.BlockShape}
    {nP j : Nat} {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {env₀ : Env} {n : Name}
    (h : (ConLeche.consBlockRecs find? q nP j rs env₀).find? n = none) : env₀.find? n = none := by
  cases hn : env₀.find? n with
  | none => rfl
  | some c =>
    have := ConLeche.find?_consBlockRecs_le (find? := find?) (q := q) (nP := nP) (m := j)
      (rs := rs) (env := env₀) n (by rw [hn]; rfl)
    rw [h] at this
    exact nomatch this

/-! ## The recursor stage's own constructor list, positionally

`checkBlockRecsRules` reads the member's constructors off `ctorsAs` at
the recursor's target and stores them with the recursor
(`BlockInstall.lean`'s `ctorsA`), so a stored recursor's fourth
component IS one of the constructors' stage's lists.  That is the one
fact the recursor lane needs to turn the constructors' stage's
STORAGE into its own `hctorsIn`, and the Verify tier's inversion of
stage (c) (`checkBlockRecsRules_facts`) does not keep it.

**Recommendation**: fold this clause into `checkBlockRecsRules_facts`
when the Verify lane next touches it. -/

section RecCtors

local macro "close_throw " h:term : tactic =>
  `(tactic| first
      | exact nomatch $h
      | exact absurd $h (by
          simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
          exact fun hh => nomatch hh)
      | exact absurd $h
          (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-- Every stored recursor's constructor list is a constructors'-stage
list, at its member's index. -/
theorem checkBlockRecsRules_ctorsIdx {envR envT : Env} {pp : BlockParts} {recNames : List Name}
    {rlvls : List Level} {cvRas : List (ConstantVal × Nat)}
    {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat} :
    ∀ {recs : List ConLeche.RecShape} {ri : Nat}
      {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))},
      ConLeche.checkBlockRecsRules (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envR
        (ConLeche.fueledOps μ F) envT pp recNames rlvls cvRas ctorsAs recs ri = .ok rs →
      ∀ r ∈ rs, ∃ c : Nat, ctorsAs[c]? = some r.2.2.2
  | [], _, rs, h => by
    simp only [ConLeche.checkBlockRecsRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro r hr
    simp at hr
  | rc :: rest, ri, rs, h => by
    unfold ConLeche.checkBlockRecsRules at h
    obtain ⟨ms, _, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨ctorsA, hctorsA, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨kss, _, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨cvRn, _, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨cvRa, nIdx⟩ := cvRn
    try simp only at h
    by_cases hlen : (ctorsA.length == ms.ctors.length) = true
    case neg => rw [if_neg hlen] at h; close_throw h
    rw [if_pos hlen] at h
    obtain ⟨rhss, _, h⟩ := ConLeche.exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := ConLeche.exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hmem
    · exact ⟨pp.recTgtAt ri, ConLeche.unwrapOr_ok hctorsA⟩
    · exact checkBlockRecsRules_ctorsIdx hrest r hmem

/-- The recursor stage, at the same fact. -/
theorem checkBlockRecK_ctorsIdx {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envC pp cvTas
      ctorsAs = .ok rs) :
    ∀ r ∈ rs, ∃ c : Nat, ctorsAs[c]? = some r.2.2.2 := by
  unfold ConLeche.checkBlockRecK at h
  obtain ⟨_, _, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨_, _, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨_, _, h⟩ := ConLeche.exceptBind_ok h
  exact checkBlockRecsRules_ctorsIdx h

end RecCtors

/-! ## The recursor stage's obligation -/

/-- **What the recursors' stage owes the tables' stage** (milestone
M5's conjunct ⑧, which `DeclBlockRun` deliberately leaves opaque): a
carrier at the post-recursor environment that
* reads every name the pre-recursor environment stores as that
  environment's carrier does (`acval` agreement),
* finds everything it found (`find?` monotonicity),
* reads every pre-recursor-bounded expression the same way
  (`denoteMeta` stability — the constructors' and formers' TYPE
  readings cross the conses), and
* keeps every member's projection slots free (`NoProjEnv`
  preservation — the generated recursor types and rule right-hand
  sides carry no projection of a member; at ONE member this is
  `Expr.NoProjAt.structRecTyR`/`structRecRhsR`).

It is four cons-monotonicities and mentions no `BlockData`: the
recursor lane proves it once, and `declBlock` consumes it. -/
@[expose] def BlockRecStaged (μ : CheckMode) {V : Type w} [SetTheory V]
    (envC : Env) (p : ConLeche.BlockShape) (nP : Nat)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (mpC : EnvModelM V μ envC) : Prop :=
  ∃ mp' : EnvModelM V μ (ConLeche.consBlockRecs envC.find? p nP 0 rs envC),
    (∀ n : Name, (envC.find? n).isSome = true → mp'.base2.acval n = mpC.base2.acval n) ∧
    (∀ (n : Name) (c : ConstantInfo), envC.find? n = some c →
      (ConLeche.consBlockRecs envC.find? p nP 0 rs envC).find? n = some c) ∧
    (∀ (ψ : Name → Nat) (dd : Nat) (e : Expr), ConstsBound envC e →
      denoteMeta mp'.base2.acval (ConLeche.consBlockRecs envC.find? p nP 0 rs envC) ψ dd e
        = denoteMeta mpC.base2.acval envC ψ dd e) ∧
    (∀ (T : Name) (i : Nat), envC.findProj? T i = none → NoProjEnv envC T i →
      NoProjEnv (ConLeche.consBlockRecs envC.find? p nP 0 rs envC) T i)

/-- **The tables' invariant crosses the recursors' conses**, by the
four facts of `BlockRecStaged` and nothing else. -/
theorem BlockTablesCore.consRecs {envC envR : Env} {mC : EnvModel V envC} {mR : EnvModel V envR}
    {d : BlockData V} {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : ConLeche.BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (h : BlockTablesCore mC d lps cvTasAll p₁ isRec A 0)
    (hag : ∀ n : Name, (envC.find? n).isSome = true → mR.acval n = mC.acval n)
    (hfind : ∀ (n : Name) (c : ConstantInfo), envC.find? n = some c → envR.find? n = some c)
    (hden : ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr), ConstsBound envC e →
      denoteMeta mR.acval envR ψ dd e = denoteMeta mC.acval envC ψ dd e)
    (hnp : ∀ (T : Name) (i : Nat), envC.findProj? T i = none →
      NoProjEnv envC T i → NoProjEnv envR T i)
    (hslot : ∀ c, c < d.k → (∃ cA, d.ctorsM c = [cA]) → d.nIdxAt c = 0 →
      ∀ j, envC.findProj? (d.memberName c) j = none) :
    BlockTablesCore mR d lps cvTasAll p₁ isRec A 0 := by
  obtain ⟨hform, hctor, hnpC⟩ := h
  have hsome : ∀ n : Name, (envC.find? n).isSome = true → (envR.find? n).isSome = true := by
    intro n hn
    cases hc : envC.find? n with
    | none => rw [hc] at hn; exact nomatch hn
    | some c => rw [hfind n c hc]; rfl
  refine ⟨fun c cvTb hc => ?_, fun c j cA hj => ?_,
    fun c hc hck h1 h2 j => hnp _ _ (hslot c hck h1 h2 j) (hnpC c hc hck h1 h2 j)⟩
  · obtain ⟨hfindT, hres, hleaf, hFD⟩ := hform c cvTb hc
    refine ⟨hfind _ _ hfindT, Expr.constsResolve_of_find hsome hres, fun ψ => ?_, ?_⟩
    · rw [hag cvTb.name (by rw [hfindT]; rfl)]; exact hleaf ψ
    · exact ⟨fun ψ => by
        rw [hden ψ 0 cvTb.type (constsBound_of_constsResolve _ hres)]; exact hFD.read ψ,
      hFD.len, hFD.bits, hFD.okTy, hFD.below, hFD.params⟩
  · obtain ⟨hfindC, hlps, hres, hread, hleaf⟩ := hctor c j cA hj
    refine ⟨hfind _ _ hfindC, hlps, Expr.constsResolve_of_find hsome hres, fun ψ => ?_,
      fun ψ => ?_⟩
    · rw [hden ψ 0 cA.1.type (constsBound_of_constsResolve _ hres)]; exact hread ψ
    · rw [hag cA.1.name (by rw [hfindC]; rfl)]; exact hleaf ψ

/-- **The P carrier survives the uniform install at `k` members.**

Two things about `hrec`, the recursor stage's obligation:

* it is stated at **`checkBlockRecK`**, the UNIFORM check, which the
  stage `checkBlockRec` runs before its reject-only conformance check
  (`checkBlockRecK_of_rec`);
* it is handed everything the CONSTRUCTORS' environment knows: the
  model `mpC`, the block data `dR` with the three records
  `blockModelAt_of_stages` consumes (`BlockNamesOk`,
  `BlockCtorsStage`, `BlockCtorsCore`) and the positional link from
  the stage's `ctorsAs` to `dR.ctorsM`, plus the recogniser's member
  names and the STORAGE of the constructors the recursors carry
  (discharged here from `checkBlockRecK_ctorsIdx` and
  `BlockCtorsCore`'s own storage clause).  Building `BlockModelAt`
  itself from those three records is the regimes' first step and is
  deliberately not done here.

The run's nine conjuncts, one stage at a time: the formers' and the
constructors' stages are `blockTablesStage_of`'s (conjuncts ①②③⑥⑦,
with the two freshness facts of conjunct ⑨ supplied here), the
constructors are consed by `stageBlockCtors` (conjunct ②'s install
half), the recursors' stage is the named `BlockRecStaged` (conjunct
⑧, which `DeclBlockRun` leaves opaque so milestone M5 changes it
alone), and the tables are `stageBlockTables` (conjunct ⑨).  The
invariant that crosses all of it is `BlockCtorsCore` → (at the
recursors) `BlockTablesCore`. -/
theorem declBlock (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : BlockParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env p₀ env₂)
    (hrec : ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
        (ctorsAsR : List (List (ConstantVal × Nat)))
        (rsR : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
        (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
        (A : Nat → (Name → Nat) → AnnotTerm)
        (fssZ : (Name → Nat) → Nat → List (List AnnotTerm)),
        -- the recursor stage's own run
        ConLeche.checkBlockRecK (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envC pp cvTasR
          ctorsAsR = .ok rsR →
        -- the recogniser's member names
        pp.toBlockShape.memberNames.Nodup →
        -- the block's REPRESENTATION at the constructors' environment,
        -- in the three records `blockModelAt_of_stages` consumes
        BlockNamesOk (V := V) dR cvTasR →
        BlockCtorsStage (V := V) μ F dR pp.lps cvTasR pp.toBlockShape isRecR A fssZ envI
          pp.ctorNamesAt →
        BlockCtorsCore mpC.base2 dR pp.lps cvTasR pp.toBlockShape isRecR A dR.k →
        (∀ c, c < ctorsAsR.length → ctorsAsR[c]? = some (dR.ctorsM c)) →
        -- the constructors' STORAGE, at the lists the recursors carry
        (∀ r ∈ rsR, ∀ cA ∈ r.2.2.2,
          ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF)) →
        -- the block's REPRESENTATION is the run's own record (lane RM49:
        -- without it `dR` is over-quantified — nothing ties its `nP`,
        -- `resSort`, operator or injections to the block, and the
        -- regimes' `BlockModelAt` cannot be built)
        (∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
            (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
          dR = blockDataOf V pp.toBlockShape env₀ ctorsAsR pp.kinds pk uOfD ppsOf) →
        -- the field kinds cover every constructor (the classification is a
        -- `mapM` over the constructors — lane RM50: without it the rules'
        -- stage's `zip` could drop rules and `nCt` would outrun them)
        (∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAsR[c]? = some ctorsA →
          (pp.kinds.getD c []).length = ctorsA.length) →
        BlockRecStaged (V := V) μ envC pp.toBlockShape pp.nP rsR mpC) :
    Nonempty (EnvModelM V μ env₂) := by
  classical
  obtain ⟨hndC₀, hndM₀, isRec, env₁, cvTas, p₁, p, ctorsAs, sortsss, kinds, isorts, rs,
    hInd, hp, hCtors, hK, -, -, hsorts, hFOk, hRec, hTbl⟩ := hrun
  subst hp
  -- ## the recogniser's facts, moved to the shape the formers' stage completed
  obtain ⟨hshape, -, -⟩ := ConLeche.blockParts?_inv hdp
  obtain ⟨-, -, -, hmembersOk, -, hClps₀, -, -, -⟩ := ConLeche.blockShape?_inv hshape
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, hmem0, -, hq, hcons, -, -, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  have hlps₀ : ∀ ms ∈ p₀.members, ms.cvT.levelParams = p₀.lps :=
    fun ms hms => (hmembersOk ms hms).1
  have hndM : p₁.memberNames.Nodup := by rw [hq]; exact hndM₀
  have hndC : (p₁.allCtors.map (·.1.name)).Nodup := by rw [hq]; exact hndC₀
  have hClps : ∀ c ∈ p₁.allCtors, c.1.levelParams = p₁.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false := by rw [hq]; exact hClps₀
  -- ## the formers' and the constructors' run, read positionally
  obtain ⟨ppsOf₀, sOf₀, hF⟩ := blockFormerFacts_of hμ mp hInd hlps₀
  obtain ⟨hlenCA, hlenSA, -⟩ := ConLeche.checkBlockCtors_inv hCtors
  have hkm : p₁.k = p₁.members.length := rfl
  have hlenCtorsAs : ctorsAs.length = p₁.k := by
    rw [hlenCA, List.length_zip, hF.lenCv, hkm]
    exact Nat.min_self _
  have hlenSortsss : sortsss.length = p₁.k := by
    rw [hlenSA, List.length_zip, hF.lenCv, hkm]
    exact Nat.min_self _
  have hmemCtors : ∀ (m : Nat), m < p₁.k →
      ∀ c ∈ (p₁.members.getD m default).ctors, c ∈ p₁.allCtors := by
    intro m hm c hc
    rw [ConLeche.BlockShape.allCtors, List.mem_flatten]
    refine ⟨_, List.mem_map.mpr ⟨_, ?_, rfl⟩, hc⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m < p₁.members.length from hm)]
    exact List.getElem_mem _
  have hfacts := fun (m : Nat) (cvTa : ConstantVal) (hm : m < p₁.k)
      (hcv : cvTas[m]? = some cvTa) =>
    blockCtorFacts_of (blockCtorRuns_of hCtors hF.nameOf m cvTa hm hcv)
      (fun c hc => hClps c (hmemCtors m hm c hc))
  -- ## the member name, read off the member list
  have hmnameEq : ∀ (m : Nat), m < p₁.k →
      p₁.memberNames.getD m .anonymous = (p₁.members.getD m default).cvT.name := by
    intro m hm
    rw [ConLeche.BlockShape.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show m < p₁.members.length from hm),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m < p₁.members.length from hm)]
    rfl
  -- ## the tables' loop's entries, positionally
  have hzipEntry : ∀ (m : Nat), m < p₁.k →
      (p₁.members.zip (ctorsAs.zip sortsss))[m]?
        = some (p₁.members.getD m default, ctorsAs.getD m [], sortsss.getD m []) := by
    intro m hm
    have hc1 : ctorsAs[m]? = some (ctorsAs.getD m []) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlenCtorsAs]; exact hm)]
      rfl
    have hs1 : sortsss[m]? = some (sortsss.getD m []) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlenSortsss]; exact hm)]
      rfl
    have hm1 : p₁.members[m]? = some (p₁.members.getD m default) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show m < p₁.members.length from hm)]
      rfl
    rw [List.getElem?_zip_eq_some]
    exact ⟨hm1, by rw [List.getElem?_zip_eq_some]; exact ⟨hc1, hs1⟩⟩
  -- ## conjunct ⑨'s two freshness facts, pulled back to the formers'
  -- environment (a name absent above a cons was absent below it)
  have hpull : ∀ n : Name,
      (ConLeche.consBlockRecs (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find? p₁ p₁.nP 0 rs
        (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)).find? n = none → env₁.find? n = none :=
    fun n h => find?_none_consBlockCtors (find?_none_consBlockRecs h)
  have hfamFree : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < p₁.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (p₁.members.getD m default).nIdx = 0 → 0 < cA.2 →
      env₁.find? (projFnName (p₁.memberNames.getD m .anonymous) 0) = none := by
    intro m cA sorts hm hcA hs hn0 hpos
    rw [hmnameEq m hm]
    exact hpull _ (blockTablesFamFree (q := p₁) (p₁.members.zip (ctorsAs.zip sortsss)) _ env₂
      hTbl m _ (hzipEntry m hm) cA sorts hcA hs hn0 hpos)
  have hprojTbl : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < p₁.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (p₁.members.getD m default).nIdx = 0 →
      env₁.find? (projTableName (p₁.memberNames.getD m .anonymous)) = none := by
    intro m cA sorts hm hcA hs hn0
    rw [hmnameEq m hm]
    exact hpull _ (blockTablesTblFree (q := p₁) (p₁.members.zip (ctorsAs.zip sortsss)) _ env₂
      hTbl m _ (hzipEntry m hm) cA sorts hcA hs hn0)
  -- ## the recursor stage IS the uniform check, read through the
  -- conformance check after it (`checkBlockRecK_of_rec`)
  have hRecK := checkBlockRecK_of_rec hRec
  -- ## the formers' and the constructors' stage
  obtain ⟨pk, uOf, ppsOf, fssZ, mpI, hN, hS, hcore, hEtaI, hfreshC⟩ :=
    blockTablesStage_of hμ mp hE hlps₀ hndM hndC hClps hInd hCtors hK hsorts hFOk
      hfamFree hprojTbl
  -- ## the constructors, consed
  have hctorsAs : ∀ c, c < ctorsAs.length →
      ctorsAs[c]? = some ((blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).ctorsM c) := by
    intro c hc
    show ctorsAs[c]? = some (ctorsAs.getD c [])
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
    rfl
  obtain ⟨mpC, hEtaC, hcoreC⟩ :=
    stageBlockCtors hμ hN hN.2.2.2 hS.toBlockCtorsStage hlenCtorsAs hctorsAs ctorsAs 0 env₁ mpI
      (fun c => by rw [Nat.zero_add]) (Nat.zero_add _) hEtaI hcore
      (fun c _ j cA hj => hfreshC c j cA hj)
  -- ## every member's projection slots, free at the constructors' environment
  have hnpEnvC : ∀ c, c < (blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).k →
      (∃ cA, (blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).ctorsM c = [cA]) →
      (blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).nIdxAt c = 0 → ∀ j,
      NoProjEnv (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
        ((blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).memberName c) j := by
    intro c hc h1 h2 j
    obtain ⟨cvTa, hcv⟩ : ∃ cvTa, cvTas[c]? = some cvTa :=
      ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact hc)⟩
    have hname : (blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).memberName c = cvTa.name :=
      (hF.nameOf c cvTa hcv).symm
    have h0 : NoProjEnv env
        ((blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).memberName c) j := by
      rw [hname]
      exact noProjEnv_of_fresh mp.base2.wf (hF.freshOf c cvTa hcv) j
    have h1' : NoProjEnv env₁
        ((blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).memberName c) j := by
      rw [hcons]
      refine noProjEnv_consBlockInds h0 (fun cvTb hcvTb => ?_)
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
      exact hS.noProjT c t cvTb hc ht j
    refine noProjEnv_consBlockCtors h1' (fun ctorsA hl cA hcA => ?_)
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hl
    obtain ⟨jj, hjj⟩ := List.getElem?_of_mem hcA
    refine hS.noProjC c t jj cA hc h1 h2 ?_ j
    show (ctorsAs.getD t [])[jj]? = some cA
    rw [List.getD_eq_getElem?_getD, ht]
    exact hjj
  -- ## every member's projection TABLE is absent at the constructors'
  -- environment: the tables' stage checked it free above the
  -- recursors, and a name absent there was absent below them
  have hslotC : ∀ c, c < (blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).k →
      (∃ cA, (blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).ctorsM c = [cA]) →
      (blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).nIdxAt c = 0 → ∀ j,
      (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).findProj?
        ((blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).memberName c) j = none := by
    intro c hc h1 h2 j
    obtain ⟨cA, hcA⟩ := h1
    have hck : c < p₁.k := hc
    have hcAs : ctorsAs.getD c [] = [cA] := by
      rw [List.getD_eq_getElem?_getD,
        hctorsAs c (by rw [hlenCtorsAs]; exact hck), hcA]
      rfl
    -- the member's sorts list is a singleton, because it is as long as
    -- its constructor list (`checkSumCtors_inv`)
    obtain ⟨sorts, hs⟩ : ∃ sorts, sortsss.getD c [] = [sorts] := by
      obtain ⟨-, -, hall⟩ := ConLeche.checkBlockCtors_inv hCtors
      obtain ⟨mc, hmc⟩ : ∃ mc, (p₁.members.zip cvTas)[c]? = some mc := by
        refine ⟨_, List.getElem?_eq_getElem ?_⟩
        rw [List.length_zip, hF.lenCv, hkm, Nat.min_self]
        exact Nat.lt_of_lt_of_eq hck hkm
      obtain ⟨ctorsA, sortss, hcs, hss, hsum⟩ := hall c mc hmc
      obtain ⟨hlc, hls, -⟩ := ConLeche.checkSumCtors_inv hsum
      have hlen1 : sortss.length = 1 := by
        rw [hls, ← hlc]
        have : ctorsA = ctorsAs.getD c [] := by
          rw [List.getD_eq_getElem?_getD, hcs]; rfl
        rw [this, hcAs]
        rfl
      match sortss, hlen1 with
      | [sorts], _ => exact ⟨sorts, by rw [List.getD_eq_getElem?_getD, hss]; rfl⟩
    have hn0 : (p₁.members.getD c default).nIdx = 0 := by
      rw [← blockNIdxs_getD (q := p₁) (j := c) (Nat.lt_of_lt_of_eq hck hkm)]
      exact h2
    have hfree := find?_none_consBlockRecs
      (blockTablesTblFree (q := p₁) (p₁.members.zip (ctorsAs.zip sortsss)) _ env₂
        hTbl c _ (hzipEntry c hck) cA sorts hcAs hs hn0)
    have hname : (blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).memberName c
        = (p₁.members.getD c default).cvT.name := hmnameEq c hck
    have hfree' : (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?
        (projTableName (p₁.members.getD c default).cvT.name) = none := hfree
    rw [hname, ConLeche.Env.findProj?, hfree']
  -- ## the constructors the RECURSORS carry are the constructors'
  -- stage's own lists, so they are stored
  have hctorsIn : ∀ r ∈ rs, ∀ cA ∈ r.2.2.2,
      ∃ cvj cnP cnF,
        (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find? cA.1.name
          = some (.ctorInfo cvj cnP cnF) := by
    intro r hr cA hcA
    obtain ⟨c, hc⟩ := checkBlockRecK_ctorsIdx hRecK r hr
    have hcl : c < ctorsAs.length := by
      have := (List.getElem?_eq_some_iff.mp hc).1
      omega
    have heq : r.2.2.2
        = (blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf).ctorsM c :=
      Option.some.inj (hc.symm.trans (hctorsAs c hcl))
    rw [heq] at hcA
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    exact ⟨cA.1, _, _, (hcoreC.2.2.2 c (by rw [hlenCtorsAs] at hcl; exact hcl) j cA hj).1⟩
  -- ## the recursors' stage, and the tables' invariant across it
  obtain ⟨mpR, hag, hfindMono, hden, hnpMono⟩ :=
    hrec (ConLeche.consBlockCtors p₁.nP ctorsAs env₁) env₁
      ((p₀.complete p₁).withKinds kinds)
      cvTas ctorsAs rs mpC (blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf) isRec
      (blockLeafZ (blockDataOf V p₁ env ctorsAs kinds pk uOf ppsOf) fssZ) fssZ
      hRecK hndM hN hS.toBlockCtorsStage hcoreC
      (fun c hc => hctorsAs c hc) hctorsIn ⟨env, pk, uOf, ppsOf, rfl⟩
      (fun c ctorsA hc => by
        obtain ⟨-, hallK⟩ := ConLeche.classifyBlockKinds_inv hK
        obtain ⟨kss, hk, hcl⟩ := hallK c ctorsA hc
        show (kinds.getD c []).length = _
        rw [List.getD_eq_getElem?_getD, hk, Option.getD_some]
        exact (ConLeche.classifyMemberKinds_inv hcl).2.2.2)
  have hcoreT :=
    (blockTablesCore_of hN hcoreC hnpEnvC).consRecs hag hfindMono hden hnpMono hslotC
  -- ## the tables
  refine stageBlockTables hN hS rfl rfl rfl (p₁.members.zip (ctorsAs.zip sortsss)) 0 _ env₂
    mpR ?_ hTbl hcoreT
  intro c e hce
  have hck : c < p₁.k := by
    have h := (List.getElem?_eq_some_iff.mp hce).1
    rw [List.length_zip, List.length_zip, hlenCtorsAs, hlenSortsss] at h
    simp only [Nat.min_self] at h
    rw [hkm]
    omega
  obtain rfl : e = (p₁.members.getD c default, ctorsAs.getD c [], sortsss.getD c []) :=
    Option.some.inj (hce.symm.trans (hzipEntry c hck))
  refine ⟨by rw [Nat.zero_add]; exact hck, ?_, ?_, ?_, ?_⟩
  · rw [Nat.zero_add]; exact (hmnameEq c hck).symm
  · rw [Nat.zero_add]
    show (p₁.members.getD c default).nIdx = p₁.nIdxs.getD c 0
    rw [blockNIdxs_getD (q := p₁) (j := c) (show c < p₁.members.length from hck)]
  · rw [Nat.zero_add]; rfl
  · intro sorts hss
    rw [Nat.zero_add]
    show sorts = (sortsss.getD c []).getD 0 []
    have hss' : sortsss.getD c [] = [sorts] := hss
    rw [hss']
    rfl

end ConLeche.Model
