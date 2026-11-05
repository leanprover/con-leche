module

public import ConLeche.Model.Inductives.FamilyRan
public import ConLeche.Model.Inductives.BlockAssembly
public import ConLeche.Model.Inductives.BlockStageTables
import ConLeche.Verify.PropWhen
import ConLeche.Model.Env.LfpHoleOp
import ConLeche.Model.Inductives.BlockCaps
import ConLeche.Model.Inductives.BlockHoleGrade
import ConLeche.Verify.Inductives.NfMemberFree
public import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Model.Inductives.BlockAccRunCont
import ConLeche.Model.Inductives.BlockHoleFold
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Semantics.Inductives.DeclBlockEta
public import ConLeche.Verify.Inductives.BlockWF
public section

/-!
# The block's representation datum, built from the install's run

One stage at a time: the formers' run (`blockFormerFacts_of`), the DUMMY pass
(`blockDummyPass`), every member's constructors read at its carrier
(`blockCtorFunsAt`), the fields with holes as the walked term's reading
there (`nfFieldsRead`, `blockAbsRead_of_run`) with the stored field
shape facts (`blockStoredShapes_of_run`), the members' index telescopes
(`blockIdxFacts_of`), the HOLE chains graded by U2 — the install's
positivity stage, run at the dummy carrier (`blockHoleGrade_of_run`,
`blockHoleChains_facts`) — the REAL pass at the
formers' HOLE leaves (`blockRealPass`, `blockLeafH`), the constructors
read again at ITS carrier, where the walked term reads alike
(`canonCrest_read_agree`: it looks up no member) — and out of that the
record `BlockData` the stages are stated over.  No field is classified.

**The record is a `def`, not a choice.**  `blockDataOf` is the datum
at chosen per-member constructor data (`BlockMemberPick`), a parameter
count and a telescope reading; every shape equation the later stages
need (`d.nP = q.nP`, `d.ctorsM`, …) is then definitional, and the two
carriers differ only in the pick (whose fields with holes they share).  `BlockData.withPhi`
installs the tuple operator and the injections over the record's own
derived fields, so `blockModelAt_of_records`' `hPhi`/`hinj` are `rfl`.
The operator is the HOLE operator (`LfpDatum.holeOp`: the
interpretation of the constructors' fields with holes), monotone by
positivity and closed by ACCESSIBILITY at every block (`closed_of_acc`,
`blockAcc_of_run`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  BlockShape BlockShape MemberShape RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The record -/

/-- **The block's representation record but for the operator and the
injections**, at a chosen per-member constructor pick. -/
@[expose] noncomputable def blockDataPre (V : Type w) [SetTheory V] (q : BlockShape)
    (pk : Nat → BlockMemberPick)
    (uOf : Nat → (Name → Nat) → Nat)
    (ppsOf : Nat → (Name → Nat) → List Term) : BlockData V where
  nP := q.nP
  k := q.k
  nInst := 0
  resSort := q.resSort
  isProp := q.isProp
  large := q.large
  memberNames := q.memberNames
  nIdxs := q.nIdxs
  shown := fun m => q.members[m]?.map (·.cvT)
  ppsM := ppsOf
  uM := uOf
  ctorsM := fun c => q.memberCtors.getD c []
  idxF := fun c j => (pk c).idxF j
  dsF := fun c j => (pk c).dsF j
  esF := fun c j => (pk c).esF j
  srcsF := fun c j => (pk c).srcsF j
  fvsPF := fun c j => (pk c).fvsPF j
  xFvsF := fun c j => (pk c).xFvsF j
  xrestF := fun c j => (pk c).xrestF j
  absFF := fun c j => (pk c).absF j
  nfFF := fun c j => (pk c).nf j
  Φ := fun _ _ X => X
  inj := fun _ _ _ _ => SetTheory.pt

/-- **The tuple operator and the injections, over the record's own
derived fields**: the hole operator of the record's fields with holes
(charter item 2), and the tagged-union injections, the point at a
`Prop`-valued block. -/
@[expose] noncomputable def BlockData.withPhi (d : BlockData V) : BlockData V :=
  { d with
    Φ := fun ψ ρp => d.toLfp.holeOp ψ ρp
    inj := fun ψ _ j fs =>
      if d.w ψ = 0 then (SetTheory.pt : V) else ConLeche.SetTheory.Tower.inj j (mkTower (fs ++ [SetTheory.pt])) }

/-- **The block's representation record**, at a pick. -/
@[expose] noncomputable def blockDataOf (V : Type w) [SetTheory V] (q : BlockShape)
    (pk : Nat → BlockMemberPick)
    (uOf : Nat → (Name → Nat) → Nat)
    (ppsOf : Nat → (Name → Nat) → List Term) : BlockData V :=
  (blockDataPre V q pk uOf ppsOf).withPhi

/-- **A member's former leaf on the HOLE chains** (charter item 2): the block operator at the constructors' fields with
holes, the operator the datum's `Φ` IS (`BlockData.withPhi`).  It
reads no field classification and no member: the formers are consed
with it. -/
@[expose] noncomputable def blockLeafH (d : BlockData V) (c : Nat) (ψ : Name → Nat) : Term :=
  blockTyG d.k (d.w ψ) (fun c' => d.uM c' ψ) (fun c' => d.IdsM c' ψ) (d.toLfp.holeChains ψ)
    (d.ppsM c ψ) c

/-! ## Small list readings -/

theorem getD_mem {α : Type} {L : List α} {j : Nat} (a : α) (hj : j < L.length) :
    L.getD j a ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

theorem getD_of_le {α : Type} {L : List α} {j : Nat} (a : α) (hj : L.length ≤ j) :
    L.getD j a = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]
  rfl

/-! ## A name absent after the formers' conses is absent before them -/

/-- The `k` formers' conses add names; they take none away. -/
theorem consBlockInds_find?_none {p₁ : BlockShape} {isRec : Bool} :
    ∀ {cvTas : List ConstantVal} {i : Nat} {env : Env} {n : Name},
      (ConLeche.consBlockInds p₁ isRec cvTas i env).find? n = none → env.find? n = none
  | [], _, _, _, h => h
  | _ :: _, _, _, _, h => find?_none_of_consB (consBlockInds_find?_none h)

/-- A term resolving before the block resolves after the `k` formers'
conses. -/
theorem consBlockInds_constsResolve {p₁ : BlockShape} {isRec : Bool} :
    ∀ (cvTas : List ConstantVal) (i : Nat) (env : Env) (e : Expr),
      e.constsResolve env = true →
      e.constsResolve (ConLeche.consBlockInds p₁ isRec cvTas i env) = true
  | [], _, _, _, h => h
  | cvT :: rest, i, env, e, h => by
    show e.constsResolve (ConLeche.consBlockInds p₁ isRec rest (i + 1)
      ⟨.indInfo cvT (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩) = true
    exact consBlockInds_constsResolve rest (i + 1) _ e (Expr.constsResolve_mono h)

/-- **A member's recursor name is reserved only if the member's is**:
`reservedBasisNames` is four `.str _ "rec"` names and twelve others,
none of them of that shape, so the four are the only way `T.str "rec"`
can be reserved — and then `T` is. -/
theorem reservedBasisNames_str_rec {T : Name}
    (h : ConLeche.reservedBasisNames.contains T = false) :
    ConLeche.reservedBasisNames.contains (T.str "rec") = false := by
  revert h
  simp +decide [ConLeche.reservedBasisNames, Name.str.injEq, ConLeche.eqName,
    ConLeche.eqReflName, ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName,
    ConLeche.emptyName, ConLeche.falseName,
    ConLeche.quotName, ConLeche.quotMkName, ConLeche.quotLiftName, ConLeche.quotIndName,
    ConLeche.quotSoundName]
  intro h1 _ _ h4 _ _ _ h8 _ h10 _ _ _ _ _ _
  exact ⟨h1, h4, h8, h10⟩

/-! ## The members' constructors, as the run checked them -/

/-- **Every member's constructors, positionally** (conjunct 2 read at
one member): the stored constant's name, level parameters, field count
and freshness, and the sum route's run that produced it. -/
theorem blockCtorRuns_of {envI : Env} {q : BlockShape} {F : Nat}
    {sortsss : List (List (List Level))}
    (hCtors : ConLeche.checkBlockCtors (m := ConLeche.CheckM) (ConLeche.fueledOps .verified F) envI envI q
      q.members = .ok sortsss) :
    ∀ (m : Nat) (cvTa : ConstantVal), m < q.k → q.formers[m]? = some cvTa →
      ConLeche.checkSumCtors (ConLeche.fueledOps .verified F) envI envI cvTa.name q.lps q.nP
          (q.nIdxs.getD m 0) q.resSort q.isProp q.large cvTa
          (q.members.getD m default).ctors
        = .ok (q.memberCtors.getD m [], sortsss.getD m []) := by
  intro m cvTa hm hcv
  obtain ⟨-, hall⟩ := ConLeche.checkBlockCtors_inv hCtors
  have hml : m < q.members.length := hm
  obtain ⟨ms, hms⟩ : ∃ ms, q.members[m]? = some ms := ⟨_, List.getElem?_eq_getElem hml⟩
  obtain ⟨sortss, hsA, hrun⟩ := hall m ms hms
  have hmsD : q.members.getD m default = ms := by
    rw [List.getD_eq_getElem?_getD, hms]; rfl
  obtain rfl : ms.cvT = cvTa := by
    rw [BlockShape.formers, List.getElem?_map, hms] at hcv
    exact Option.some.inj hcv
  have hnIdx : q.nIdxs.getD m 0 = ms.nIdx := by
    rw [BlockShape.nIdxs, List.getD_eq_getElem?_getD, List.getElem?_map, hms]; rfl
  have hcs : q.memberCtors.getD m [] = ms.ctors := by
    rw [BlockShape.memberCtors, List.getD_eq_getElem?_getD, List.getElem?_map, hms]; rfl
  rw [hmsD, hnIdx, hcs, List.getD_eq_getElem?_getD, hsA]
  exact hrun

/-- **One member's constructors, as stored**: `blockCtorFuns_of`'s
`hrunOf` at a block member. -/
theorem blockCtorFacts_of {envI : Env} {q : BlockShape} {F : Nat} {cvTa : ConstantVal} {m : Nat}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hrun : ConLeche.checkSumCtors (ConLeche.fueledOps .verified F) envI envI cvTa.name q.lps q.nP
        (q.nIdxs.getD m 0) q.resSort q.isProp q.large cvTa (q.members.getD m default).ctors
      = .ok (ctorsA, sortss))
    (hClps : ∀ c ∈ (q.members.getD m default).ctors, c.1.levelParams = q.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false) :
    (ctorsA.length = (q.members.getD m default).ctors.length ∧
      sortss.length = (q.members.getD m default).ctors.length) ∧
    ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ (c : ConstantVal × Nat) (sorts : List Level),
        (q.members.getD m default).ctors[j]? = some c ∧
        cA.1.name = c.1.name ∧ cA.2 = c.2 ∧ cA.1.levelParams = q.lps ∧
        envI.find? cA.1.name = none ∧ cA.1.type.constsResolve envI = true ∧
        ConLeche.reservedBasisNames.contains cA.1.name = false ∧
        sortss[j]? = some sorts ∧
        (cA.1.type.stripPis (q.nP + cA.2)).isSome = true ∧
        (cA.1.type.hasFvar = false ∧
          ∃ stype, inferTypeCore .verified false envI F 0 cA.1.type = .ok stype) ∧
        ConLeche.checkSumCtor (ConLeche.fueledOps .verified F) envI envI cvTa.name q.lps q.nP
          (q.nIdxs.getD m 0) q.resSort q.isProp q.large c.1 cA.2 cvTa = .ok (cA.1, sorts) := by
  obtain ⟨hlenA, hlenS, hall⟩ := ConLeche.checkSumCtors_inv hrun
  refine ⟨⟨hlenA, hlenS⟩, fun j cA hj => ?_⟩
  have hjl : j < (q.members.getD m default).ctors.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1; omega
  obtain ⟨hnF, sorts, hsj, hCtor⟩ :=
    hall j ((q.members.getD m default).ctors[j]) cA (List.getElem?_eq_getElem hjl) hj
  obtain ⟨⟨heq, hccvC⟩, ⟨cbs, es, hstrip, -⟩, -⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨hfindC, -, -, -, hfvC, stype, -, -, htrC, hstC, -⟩ :=
    ConLeche.checkConstantVal_inv hccvC
  have hmem : (q.members.getD m default).ctors[j] ∈ (q.members.getD m default).ctors :=
    List.getElem_mem hjl
  refine ⟨_, sorts, List.getElem?_eq_getElem hjl, by rw [heq], hnF, ?_, ?_, ?_,
    ?_, hsj, ?_, ⟨?_, stype, ?_⟩,
    by rw [hnF]; exact hCtor⟩
  · rw [heq]; exact (hClps _ hmem).1
  · show Env.find? _ cA.1.name = none
    rw [heq]; exact hfindC
  · show Expr.constsResolve _ cA.1.type = true
    rw [heq]; exact htrC
  · rw [heq]; exact (hClps _ hmem).2
  · rw [hnF, hstrip]; rfl
  · rw [heq]; exact hfvC
  · rw [heq]; exact hstC

/-! ## The η side conditions of the two former passes -/

/-- A name found stays found across a cons. -/
theorem find?_isSome_consB {c : ConstantInfo} {env : Env} {n : Name}
    (h : (env.find? n).isSome = true) :
    (((⟨c :: env.consts, env.tables⟩ : Env)).find? n).isSome = true := by
  rw [ConLeche.Env.find?_cons]
  split
  · rfl
  · exact h

/-- A name found before the formers' conses is found after them. -/
theorem consBlockInds_find?_isSome_mono {p₁ : BlockShape} {isRec : Bool} :
    ∀ (cvTas : List ConstantVal) (i : Nat) (env : Env) (n : Name),
      (env.find? n).isSome = true →
      ((ConLeche.consBlockInds p₁ isRec cvTas i env).find? n).isSome = true
  | [], _, _, _, h => h
  | cvT :: rest, i, env, n, h => by
    show ((ConLeche.consBlockInds p₁ isRec rest (i + 1)
      ⟨.indInfo cvT (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩).find? n).isSome = true
    exact consBlockInds_find?_isSome_mono rest (i + 1) _ n (find?_isSome_consB h)

/-- **Every former is stored after the `k` conses.** -/
theorem consBlockInds_find?_isSome {p₁ : BlockShape} {isRec : Bool} :
    ∀ (cvTas : List ConstantVal) (i j : Nat) (env : Env) (cvTa : ConstantVal),
      cvTas[j]? = some cvTa →
      (((ConLeche.consBlockInds p₁ isRec cvTas i env).find? cvTa.name).isSome) = true
  | [], _, _, _, _, h => by simp at h
  | cvT :: rest, i, 0, env, cvTa, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    show ((ConLeche.consBlockInds p₁ isRec rest (i + 1)
      ⟨.indInfo cvT (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩).find? cvTa.name).isSome
      = true
    refine consBlockInds_find?_isSome_mono rest (i + 1) _ cvTa.name ?_
    have hn : (ConstantInfo.indInfo cvT (ConLeche.blockCapsAt p₁ i isRec)).name = cvT.name := rfl
    rw [← h, ← hn, ConLeche.Env.find?_cons_self]
    rfl
  | cvT :: rest, i, j + 1, env, cvTa, h => by
    simp only [List.getElem?_cons_succ] at h
    show ((ConLeche.consBlockInds p₁ isRec rest (i + 1)
      ⟨.indInfo cvT (ConLeche.blockCapsAt p₁ i isRec) :: env.consts, env.tables⟩).find? cvTa.name).isSome
      = true
    exact consBlockInds_find?_isSome rest (i + 1) j _ cvTa h

/-- A declared former, found at the install of distinct names. -/
theorem consBlockInds_find?_at {q : BlockShape} {isRec : Bool} :
    ∀ (dcl : List ConstantVal) (i j : Nat) (env : Env) (cv : ConstantVal),
      (dcl.map (·.name)).Nodup → dcl[j]? = some cv →
      (ConLeche.consBlockInds q isRec dcl i env).find? cv.name
        = some (.indInfo cv (ConLeche.blockCapsAt q (i + j) isRec))
  | [], _, _, _, _, _, h => nomatch h
  | c :: rest, i, 0, env, cv, hnd, h => by
    obtain rfl : c = cv := by simpa using h
    show (ConLeche.consBlockInds q isRec rest (i + 1) _).find? c.name = _
    have hne : ∀ c' ∈ rest, c'.name ≠ c.name := fun c' hc' he =>
      (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨c', hc', he⟩)
    rw [ConLeche.Semantics.consBlockInds_find?_of_ne hne, Nat.add_zero]
    exact ConLeche.Env.find?_cons_self (.indInfo c (ConLeche.blockCapsAt q i isRec)) env
  | c :: rest, i, j + 1, env, cv, hnd, h => by
    show (ConLeche.consBlockInds q isRec rest (i + 1) _).find? cv.name = _
    rw [consBlockInds_find?_at rest (i + 1) j _ cv (List.nodup_cons.mp hnd).2 (by simpa using h)]
    congr 3
    omega

/-- **The two former passes' η side conditions**, off the
constructors' freshness at the environment holding all `k` formers: a
member's η constructor is one of ITS OWN constructors, which is fresh
there — so it is no former's name, and it was fresh before the block
too. -/
theorem blockEtaSide_of {env envI : Env} {q : BlockShape} {F : Nat} {isRec : Bool}
    {dcl : List ConstantVal}
    {sortsss : List (List (List Level))}
    (hcons : envI = ConLeche.consBlockInds q isRec dcl 0 env)
    (hdcl : ∀ (j : Nat) (cvTb : ConstantVal), q.formers[j]? = some cvTb →
      ∃ cvS, dcl[j]? = some cvS ∧ cvS.name = cvTb.name)
    (hlenCv : q.formers.length = q.k)
    (hCtors : ConLeche.checkBlockCtors (m := ConLeche.CheckM) (ConLeche.fueledOps .verified F) envI envI q
      q.members = .ok sortsss)
    (hClps : ∀ c ∈ q.allCtors, c.1.levelParams = q.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false) :
    (∀ (j j' : Nat) (cvTa cvTb : ConstantVal), q.formers[j]? = some cvTa →
        q.formers[j']? = some cvTb → (ConLeche.blockCapsAt q j isRec).eta = true →
        cvTb.name ≠ (ConLeche.blockCapsAt q j isRec).etaCtor) ∧
    (∀ (j : Nat) (cvTb : ConstantVal), q.formers[j]? = some cvTb →
        (ConLeche.blockCapsAt q j isRec).eta = true →
        env.find? (ConLeche.blockCapsAt q j isRec).etaCtor = none) := by
  -- at an η-capable member the record names that member's ONE
  -- constructor, which the run stored and found fresh
  have hkey : ∀ (j : Nat) (cvTa : ConstantVal), q.formers[j]? = some cvTa →
      (ConLeche.blockCapsAt q j isRec).eta = true →
      envI.find? (ConLeche.blockCapsAt q j isRec).etaCtor = none := by
    intro j cvTa hj he
    have hjk : j < q.k := by
      have := (List.getElem?_eq_some_iff.mp hj).1; rwa [hlenCv] at this
    obtain ⟨c, hc, hcaps⟩ | hcaps := blockCapsAt_cases q j isRec
    · have hrun := blockCtorRuns_of hCtors j cvTa hjk hj
      obtain ⟨⟨hlenA, -⟩, hfacts⟩ := blockCtorFacts_of hrun (fun c' hc' => hClps c' (by
        rw [BlockShape.allCtors, List.mem_flatten]
        exact ⟨_, List.mem_map.mpr ⟨_, by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < q.members.length from hjk)]
          exact ⟨List.getElem_mem _, rfl⟩⟩, hc'⟩))
      rw [hc] at hlenA
      obtain ⟨cA, hcA⟩ : ∃ cA, (q.memberCtors.getD j [])[0]? = some cA :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlenA]; exact Nat.zero_lt_one)⟩
      obtain ⟨c', -, hc', hname, -, -, hfresh, -⟩ := hfacts 0 cA hcA
      rw [hc] at hc'
      obtain rfl : c = c' := by simpa using hc'
      rw [hcaps]
      show envI.find? c.1.name = none
      rw [← hname]; exact hfresh
    · rw [hcaps] at he; exact nomatch he
  refine ⟨fun j j' cvTa cvTb hj hj' he hh => ?_, fun j cvTb hj he => ?_⟩
  · have hsome : ((envI.find? cvTb.name).isSome) = true := by
      obtain ⟨cvS, hS, hn⟩ := hdcl j' cvTb hj'
      rw [← hn, hcons]; exact consBlockInds_find?_isSome _ _ _ _ _ hS
    rw [hh, hkey j cvTa hj he] at hsome
    exact nomatch hsome
  · have := hkey j cvTb hj he
    rw [hcons] at this
    exact consBlockInds_find?_none this

/-! ## Coverage at the formers' carrier -/

/-- **Coverage across the formers' cons**: a carrier of the formers'
environment that keeps every old name's leaf is covered (rebuilt with the
input's recorded list) with the block's members exempt, where the input
is covered — what the walk's container case reads (`ContCover`,
`contCover_of`) at the dummy and the real carrier. -/
theorem lfpCover_formers (mp : EnvModelM V env) {envI : Env} {q : BlockShape} {isRec : Bool}
    {dcl : List ConstantVal}
    (hcons : envI = ConLeche.consBlockInds q isRec dcl 0 env)
    (mpX : EnvModelM V envI)
    (hfresh : ∀ cvTb ∈ dcl, env.find? cvTb.name = none)
    (hagX : ∀ n : Name, (∀ cvTb ∈ dcl, n ≠ cvTb.name) → mpX.base2.acval n = mp.base2.acval n)
    {names : List Name} (hnames : ∀ cvTb ∈ dcl, cvTb.name ∈ names)
    (hex : ∀ n ∈ names, env.find? n = none) :
    LfpCover mp [] → ∃ mk : EnvModelM V envI, mk.base2 = mpX.base2 ∧
      mk.lfpBlocks = mp.lfpBlocks ∧ LfpCover mk names := by
  intro h0
  obtain ⟨newI, hnewI, hnewIall⟩ := consBlockInds_consts (p₁ := q) (isRec := isRec) dcl 0 env
  have henv : envI.consts = newI ++ env.consts := by rw [hcons]; exact hnewI
  obtain ⟨mk, hbk, hlk, hcov⟩ := lfpCover_append (ex := []) (ex' := names) mp mpX (new := newI) henv
    (by rw [hcons]; exact consBlockInds_tables dcl 0 env)
    (fun n ci hf => by
      have hfr : ∀ c ∈ newI, env.find? c.name = none := by
        intro c hc
        obtain ⟨cv, hcv, j, rfl⟩ := hnewIall c hc
        exact hfresh cv hcv
      show List.find? _ _ = _
      rw [henv]
      exact find?_append_of_fresh hfr hf)
    (fun n hn => hagX n fun cvTb hcvTb h => by
      rw [h, hfresh cvTb hcvTb] at hn
      exact nomatch hn)
    (fun _ h => nomatch h)
    (fun n hn => Or.inr (hex n hn))
    (fun c hc cv caps h => by
      obtain ⟨cv', hcv', j, rfl⟩ := hnewIall c hc
      exact hnames _ hcv')
    (fun c hc C hC => by
      obtain ⟨cv', -, j, rfl⟩ := hnewIall c hc
      simp [ctorEntry] at hC)
  exact ⟨mk, hbk, hlk, hcov h0⟩

/-- The stage's telescopes are the block's members'. -/
theorem blockMembers_read {V : Type w} [SetTheory V] {q : BlockShape}
    {pk : Nat → BlockMemberPick}
    {uOf : Nat → (Name → Nat) → Nat} {ppsOf : Nat → (Name → Nat) → List Term}
    {cvTas : List ConstantVal}
    (hN : BlockNamesOk (V := V) (blockDataOf V q pk uOf ppsOf) cvTas)
    (hshown : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
      (blockDataOf V q pk uOf ppsOf).shown m = some cvTa) :
    q.members.map (·.cvT) = cvTas := by
  have hlen : cvTas.length = q.members.length := hN.2.2
  refine List.ext_getElem? fun i => ?_
  cases hc : cvTas[i]? with
  | some cvTa =>
    rw [List.getElem?_map]
    exact hshown i cvTa hc
  | none =>
    have hi : cvTas.length ≤ i := List.getElem?_eq_none_iff.mp hc
    rw [List.getElem?_eq_none (by simp; omega)]

/-! ## The constructors' stage, from the run -/

set_option maxHeartbeats 1600000 in
/-- **The block's representation record and the constructors' stage's
obligation, from the install's run**.  The two former passes
(`blockDummyPass`, `blockRealPass`) around the members' constructor
readings (`blockCtorFunsAt`); the formers are consed with the block
operator at the HOLE chains (`blockLeafH`), graded by the positivity
stage's run (`hPos`, U2) at the dummy carrier; the record is
`blockDataOf` at the REAL pick, which shares the dummy pick's fields
with holes and normal forms. -/
theorem blockTablesStage_of {F : Nat} {env envI : Env}
    {p₀ : BlockShape} {isRec : Bool} {q : BlockShape}
    {sortsss : List (List (List Level))}
    {isorts : List (List Level)}
    (mp : EnvModelM V env) (hE : ConLeche.EtaFamiliesClosed env)
    (hlps₀ : ∀ ms ∈ p₀.members, ms.cvT.levelParams = p₀.lps)
    (hAt : ∀ ms ∈ p₀.members, ConLeche.MemberAt F env p₀.nP ms)
    (hndM : q.memberNames.Nodup)
    (hboolM : ConLeche.boolTrueName ∉ q.memberNames ∧ ConLeche.boolFalseName ∉ q.memberNames)
    (hndC : (q.allCtors.map (·.1.name)).Nodup)
    (hClps : ∀ c ∈ q.allCtors, c.1.levelParams = q.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false)
    (hInd : ConLeche.checkBlockInds (m := ConLeche.CheckM) (ConLeche.fueledOps .verified F) env p₀ isRec
      = .ok (envI, q))
    (hCtors : ConLeche.checkBlockCtors (m := ConLeche.CheckM) (ConLeche.fueledOps .verified F) envI envI q
      q.members = .ok sortsss)
    (hsorts : ConLeche.checkBlockIdxSorts (m := ConLeche.CheckM) (ConLeche.fueledOps .verified F) envI q
      q.members = .ok isorts)
    -- the positivity stage (`DeclBlockRun` 3): U2 grades the fields with holes
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × ConLeche.NestState}
    (hPos : ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps .verified F) envI
      envI.find? q = .ok posKs)
    -- the input's coverage (the walk's container case reads the containers' clauses)
    (hcovIn : LfpCover mp []) (hRan : FamilyRan mp) (hx : EnvExt env envI) :
    ∃ (pk : Nat → BlockMemberPick) (uOf : Nat → (Name → Nat) → Nat)
      (ppsOf : Nat → (Name → Nat) → List Term)
      (mpI : EnvModelM V envI),
      BlockNamesOk (V := V) (blockDataOf V q pk uOf ppsOf) q.formers ∧
      BlockTablesStage (V := V) F (blockDataOf V q pk uOf ppsOf) q.lps q.formers
        q isRec (blockLeafH (blockDataOf V q pk uOf ppsOf)) envI
        q.ctorNamesAt (fun m => (sortsss.getD m []).getD 0 []) ∧
      BlockCtorsCore mpI.base2 (blockDataOf V q pk uOf ppsOf) q.lps q.formers
        q isRec (blockLeafH (blockDataOf V q pk uOf ppsOf)) 0 ∧
      ConLeche.BlockEtaInv envI q.memberNames q.ctorNamesAt ∧
      (∀ (c j : Nat) (cA : ConstantVal × Nat),
        ((blockDataOf V q pk uOf ppsOf).ctorsM c)[j]? = some cA →
        envI.find? cA.1.name = none) ∧
      (∀ (c j : Nat) (cA : ConstantVal × Nat),
        ((blockDataOf V q pk uOf ppsOf).ctorsM c)[j]? = some cA →
        (blockDataOf V q pk uOf ppsOf).nfFF c j = (posKs.2.1.getD c []).getD j default) ∧
      -- every name off the block keeps its leaf
      ∀ n : Name, (∀ cvTb ∈ q.formers, n ≠ cvTb.name) → mpI.base2.acval n = mp.base2.acval n := by
  classical
  -- the run's shape: the k formers consed at once
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, hmem0, hq, hcons, -, -, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  have hqm : q.members = p₀.members := by rw [hq]; rfl
  have hne : 0 < q.members.length := by rw [hqm, hmem0]; simp
  have hlenN : q.memberNames.length = q.members.length := by
    show (q.members.map _).length = _; simp
  have hlenNI : q.nIdxs.length = q.memberNames.length := by
    show (q.members.map _).length = _; rw [hlenN]; simp
  -- the formers' data
  obtain ⟨ppsOf, sOf, hF⟩ := blockFormerFacts_of mp hInd hlps₀ hAt
  -- the η side conditions of the two passes
  have hdclOf := hF.dclAt
  have hofDcl := hF.ofDcl
  obtain ⟨hetaNe, hetaFresh⟩ :=
    blockEtaSide_of hcons hdclOf hF.lenCv hCtors hClps
  -- the constructors' lists, positionally
  have hCR := blockCtorRuns_of hCtors
  have hlenCtorsAs₀ : q.memberCtors.length = q.k := by simp [BlockShape.memberCtors, BlockShape.k]
  have hmcv : q.members.map (·.cvT) = q.formers := rfl
  have hlenCtorsAs : q.memberCtors.length = q.k := hlenCtorsAs₀
  have hCA : ∀ m, m < q.k → q.memberCtors[m]? = some (q.memberCtors.getD m []) := by
    intro m hm
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hlenCtorsAs]; exact hm)]
    rfl
  -- the constructors' own facts, per member
  have hmemCtors : ∀ (m : Nat), m < q.k →
      ∀ c ∈ (q.members.getD m default).ctors, c ∈ q.allCtors := by
    intro m hm c hc
    rw [ConLeche.BlockShape.allCtors, List.mem_flatten]
    refine ⟨_, List.mem_map.mpr ⟨_, ?_, rfl⟩, hc⟩
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show m < q.members.length from hm)]
    exact List.getElem_mem _
  have hfacts : ∀ (m : Nat) (cvTa : ConstantVal), m < q.k → q.formers[m]? = some cvTa →
      ((q.memberCtors.getD m []).length = (q.members.getD m default).ctors.length ∧
        (sortsss.getD m []).length = (q.members.getD m default).ctors.length) ∧
      ∀ (j : Nat) (cA : ConstantVal × Nat), (q.memberCtors.getD m [])[j]? = some cA →
        ∃ (c : ConstantVal × Nat) (sorts : List Level),
          (q.members.getD m default).ctors[j]? = some c ∧
          cA.1.name = c.1.name ∧ cA.2 = c.2 ∧ cA.1.levelParams = q.lps ∧
          envI.find? cA.1.name = none ∧ cA.1.type.constsResolve envI = true ∧
          ConLeche.reservedBasisNames.contains cA.1.name = false ∧
          (sortsss.getD m [])[j]? = some sorts ∧
          (cA.1.type.stripPis (q.nP + cA.2)).isSome = true ∧
          (cA.1.type.hasFvar = false ∧
            ∃ stype, inferTypeCore .verified false envI F 0 cA.1.type = .ok stype) ∧
          ConLeche.checkSumCtor (ConLeche.fueledOps .verified F) envI envI cvTa.name q.lps q.nP
            (q.nIdxs.getD m 0) q.resSort q.isProp q.large c.1 cA.2 cvTa = .ok (cA.1, sorts) :=
    fun m cvTa hm hcv =>
      blockCtorFacts_of (hCR m cvTa hm hcv)
        (fun c hc => hClps c (hmemCtors m hm c hc))
  -- ## the DUMMY pass: the k formers at the EMPTY chain lists
  obtain ⟨mpD, hEclD, hFDD, hdclD, hfindD₀, hagD⟩ := blockDummyPass mp hInd hF hndM hE hetaNe hetaFresh
  have hfindD := formerStored_of hF.lenDcl hdclD hfindD₀
  -- coverage at the dummy carrier, the members exempt (the walk's container case)
  have hmemFresh : ∀ cvTb ∈ q.formers, env.find? cvTb.name = none := by
    intro cvTb hcvTb
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
    exact hF.freshOf t cvTb ht
  have hmemNames : ∀ cvTb ∈ q.formers, cvTb.name ∈ q.memberNames := by
    intro cvTb hcvTb
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
    have htk : t < q.members.length := by
      have := (List.getElem?_eq_some_iff.mp ht).1; rw [hF.lenCv] at this; exact this
    rw [hF.nameOf t cvTb ht]
    exact getD_mem _ (by rw [hlenN]; exact htk)
  have hnamesFresh : ∀ n ∈ q.memberNames, env.find? n = none := by
    intro n hn
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hn
    have htk : t < q.k := by
      have := (List.getElem?_eq_some_iff.mp ht).1; rw [hlenN] at this; exact this
    obtain ⟨cvTb, hcv⟩ : ∃ cvTb, q.formers[t]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact htk)⟩
    have hname := hF.nameOf t cvTb hcv
    rw [List.getD_eq_getElem?_getD, ht] at hname
    rw [← show cvTb.name = n from hname]
    exact hF.freshOf t cvTb hcv
  have hcovD : ∃ mk : EnvModelM V envI, mk.base2 = mpD.base2 ∧
      LfpCover mk q.memberNames ∧ ∀ F, FamilyRead mk F :=
    (lfpCover_formers mp hcons mpD
      (fun cvS hS => by
        obtain ⟨cvTb, hb, hn⟩ := hofDcl cvS hS
        rw [hn]; exact hmemFresh cvTb hb)
      (fun n hn => hagD n fun cvTb hb => by
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hb
        obtain ⟨cvS, hS, hnm⟩ := hdclOf j cvTb hj
        rw [← hnm]; exact hn cvS (List.mem_of_getElem? hS))
      (fun cvS hS => by
        obtain ⟨cvTb, hb, hn⟩ := hofDcl cvS hS
        rw [hn]; exact hmemNames cvTb hb)
      hnamesFresh hcovIn).imp
      fun _ h => ⟨h.1, h.2.2, hRan.read hx.find hx.table fun D hD => by rw [← h.2.1]; exact hD⟩
  -- ## the members' index telescopes, at the dummy carrier
  obtain ⟨uOf, hIdxOf, hUparams⟩ :=
    blockIdxFacts_of (isRec := isRec) (ppsOf := ppsOf) mpD hsorts
      (fun j cvTb hj => (hfindD j cvTb hj).1) hFDD hF.lpsOf
  -- ## the members' constructors, read at the dummy carrier
  have hpickOf : ∀ mp' : EnvModelM V envI,
      (∀ (j : Nat) (cvTb : ConstantVal), q.formers[j]? = some cvTb →
        FormerStored mp'.base2 cvTb (ConLeche.blockCapsAt q j isRec)) →
      ∀ m : Nat, ∃ pk : BlockMemberPick, m < q.k →
      ∀ (j : Nat) (cA : ConstantVal × Nat), (q.memberCtors.getD m [])[j]? = some cA →
        BlockCtorDataI mp'.base2 (q.memberNames.getD m .anonymous)
          q.lps cA.1 q.nP cA.2 (q.nIdxs.getD m 0) q.resSort q.isProp q.large
          (pk.idxF j) (pk.dsF j) (pk.esF j) (pk.srcsF j)
          (pk.fvsPF j) (pk.xFvsF j) (pk.xrestF j) := by
    intro mp' hfind m
    by_cases hm : m < q.k
    · obtain ⟨cvTa, hcv⟩ : ∃ cvTa, q.formers[m]? = some cvTa :=
        ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact hm)⟩
      obtain ⟨pk, hpk⟩ := blockCtorFunsAt mp' hcv hF.nameOf hF.lpsOf hfind
        (fun j cA hj => by
          obtain ⟨c, sorts, -, -, -, -, -, -, -, -, -, -, hCtor⟩ :=
            (hfacts m cvTa hm hcv).2 j cA hj
          exact ⟨c, sorts, hCtor⟩)
      exact ⟨pk, fun _ => hpk⟩
    · exact ⟨⟨fun _ => [], fun _ _ => [], fun _ _ => [], fun _ => [], fun _ => [], fun _ => [],
        fun _ => .bvar 0, fun _ _ => [], fun _ => .bvar 0⟩, fun hh => absurd hh hm⟩
  obtain ⟨pk₀, hpk₀, hnf₀, habs₀⟩ : ∃ pk₀ : Nat → BlockMemberPick, (∀ m : Nat, m < q.k →
      ∀ (j : Nat) (cA : ConstantVal × Nat), (q.memberCtors.getD m [])[j]? = some cA →
        BlockCtorDataI mpD.base2 (q.memberNames.getD m .anonymous)
          q.lps cA.1 q.nP cA.2 (q.nIdxs.getD m 0) q.resSort q.isProp q.large
          ((pk₀ m).idxF j) ((pk₀ m).dsF j) ((pk₀ m).esF j) ((pk₀ m).srcsF j)
          ((pk₀ m).fvsPF j) ((pk₀ m).xFvsF j) ((pk₀ m).xrestF j)) ∧
      -- the positivity walk's normal forms (the run's output)
      (∀ (m j : Nat), (pk₀ m).nf j = if j < (q.memberCtors.getD m []).length
        then (posKs.2.1.getD m []).getD j default else .bvar 0) ∧
      -- the fields with holes: the normal form's reading at the dummy carrier
      ∀ (m j : Nat) (ψ : Name → Nat), (pk₀ m).absF j ψ
        = nfFieldsRead mpD.base2.acval envI (q.nP + q.k) ((q.memberCtors.getD m []).getD j default).2
            ((pk₀ m).nf j) ψ :=
    ⟨fun m => { (hpickOf mpD (fun j cvTb hj => (hfindD j cvTb hj).1) m).choose with
        nf := fun j => if j < (q.memberCtors.getD m []).length
          then (posKs.2.1.getD m []).getD j default else .bvar 0
        absF := fun j ψ => nfFieldsRead mpD.base2.acval envI (q.nP + q.k)
          ((q.memberCtors.getD m []).getD j default).2 (if j < (q.memberCtors.getD m []).length
            then (posKs.2.1.getD m []).getD j default else .bvar 0) ψ },
      fun m => (hpickOf mpD (fun j cvTb hj => (hfindD j cvTb hj).1) m).choose_spec,
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  -- ## the readings every member's data is taken against
  have hProp : q.isProp = (Level.isEquiv q.resSort .zero == some true) := by rw [hq]; rfl
  have hProp' : q.isProp = true → (Level.isEquiv q.resSort .zero == some true) = true :=
    fun h => by rw [← hProp]; exact h
  have hcvOf : ∀ t : Nat, t < q.k → ∃ cvTb, q.formers[t]? = some cvTb :=
    fun t ht => ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact ht)⟩
  have hlenPpsOf : ∀ (t : Nat), t < q.k → ∀ ψ : Name → Nat,
      (ppsOf t ψ).length = q.nP + q.nIdxs.getD t 0 := by
    intro t ht ψ
    obtain ⟨cvTb, hcv⟩ := hcvOf t ht
    exact (hF.fdOf t cvTb hcv).len ψ
  have hρpOf : ∀ (ψ : Name → Nat) (ρp : Nat → V) (m : Nat), m < q.k →
      Sat V (((ppsOf m ψ).take q.nP)).reverse ρp →
      ∀ c, c < q.k → Sat V (((ppsOf c ψ).take q.nP)).reverse ρp :=
    fun ψ ρp m hm hρ c hc => (hF.paramsIff m c hm hc ψ ρp).mp hρ
  have hleafOfD : ∀ (t : Nat), t < q.k → ∀ ψ : Name → Nat, ∃ B,
      mpD.base2.acval (q.memberNames.getD t .anonymous) ψ
        = mkLamsAV (ppsOf t ψ) B := by
    intro t ht ψ
    obtain ⟨cvTb, hcv⟩ := hcvOf t ht
    rw [← hF.nameOf t cvTb hcv, (hfindD t cvTb hcv).2 ψ]
    exact ⟨_, rfl⟩
  -- ## the DUMMY record: the field lists the members' leaves are built over
  let dZ : BlockData V := blockDataOf V q pk₀ uOf ppsOf
  have hlenFssZ : ∀ (m : Nat) (ψ : Name → Nat),
      (dZ.Fss m ψ).length = (q.memberCtors.getD m []).length := by
    intro m ψ
    show (fssOfR _ _).length = _
    rw [fssOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hlenEssZ : ∀ (m : Nat) (ψ : Name → Nat),
      (dZ.Ess m ψ).length = (q.memberCtors.getD m []).length := by
    intro m ψ
    show (essOfR _).length = _
    rw [essOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hFssZD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (q.memberCtors.getD m [])[j]? = some cA →
      (dZ.Fss m ψ).getD j [] = (((pk₀ m).dsF j ψ).drop q.nP) :=
    fun _ _ _ _ hj => fssOfR_fixCtorDataList_getD hj
  have hEssZD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (q.memberCtors.getD m [])[j]? = some cA → (dZ.Ess m ψ).getD j [] = (pk₀ m).esF j ψ :=
    fun _ _ _ _ hj => essOfR_fixCtorDataList_getD hj
  have hlenFsZ : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      m < q.k → (q.memberCtors.getD m [])[j]? = some cA →
      ((dZ.Fss m ψ).getD j []).length = cA.2 := by
    intro m j cA ψ hm hj
    rw [hFssZD m j cA ψ hj]
    simp [(hpk₀ m hm j cA hj).len ψ]
  -- ## the leaves' bookkeeping: lengths, bounds, level parameters
  have hkN : q.k = q.members.length := rfl
  have hnIdxsNil : ∀ c : Nat, ¬ c < q.k → q.nIdxs.getD c 0 = 0 := by
    intro c hc
    rw [hkN] at hc
    exact getD_of_le 0 (by rw [hlenNI, hlenN]; omega)
  have hppsNil : ∀ c : Nat, ¬ c < q.k → ∀ ψ : Name → Nat, ppsOf c ψ = [] := by
    intro c hc ψ
    refine hF.ppsNil c ?_ ψ
    rw [List.getElem?_eq_none (by rw [hF.lenCv]; omega)]
  have hIdsLen : ∀ (c : Nat) (ψ : Name → Nat),
      ((((ppsOf c ψ).drop q.nP))).length = q.nIdxs.getD c 0 := by
    intro c ψ
    by_cases hc : c < q.k
    · simp [hlenPpsOf c hc ψ]
    · rw [hppsNil c hc ψ, hnIdxsNil c hc]; simp
  have hIdsBelow : ∀ (c : Nat) (ψ : Name → Nat),
      DomsBelow q.nP (((ppsOf c ψ).drop q.nP)) := by
    intro c ψ
    by_cases hc : c < q.k
    · obtain ⟨cvTb, hcv⟩ := hcvOf c hc
      have h := (DomsBelow.drop q.nP ((hF.fdOf c cvTb hcv).below ψ))
      rwa [Nat.zero_add] at h
    · rw [hppsNil c hc ψ]
      simp only [List.drop_nil]
      trivial
  have hcdsParams : ∀ (c : Nat) (ψ₁ ψ₂ : Name → Nat), (∀ n ∈ q.lps, ψ₁ n = ψ₂ n) →
      dZ.cds c ψ₁ = dZ.cds c ψ₂ := by
    intro c ψ₁ ψ₂ hφ
    by_cases hc : c < q.k
    · obtain ⟨cvTa, hcv⟩ := hcvOf c hc
      refine fixCtorDataList_congr (q.memberCtors.getD c []) 0 fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ : ∃ cAi, (q.memberCtors.getD c [])[i]? = some cAi :=
        ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨-, -, -, -, -, hlpsi, -⟩ := (hfacts c cvTa hc hcv).2 i cAi hi'
      have hφ' : ∀ n ∈ cAi.1.levelParams, ψ₁ n = ψ₂ n := fun n hn => hφ n (by rwa [← hlpsi])
      have hD := hpk₀ c hc i cAi hi'
      obtain ⟨h1, h2⟩ := hD.params ψ₁ ψ₂ hφ'
      exact ⟨h1, h2, rfl, rfl⟩
    · have hnil : q.memberCtors.getD c [] = [] := getD_of_le [] (by rw [hlenCtorsAs]; omega)
      show fixCtorDataList _ _ _ _ _ _ (q.memberCtors.getD c []) 0
        = fixCtorDataList _ _ _ _ _ _ (q.memberCtors.getD c []) 0
      rw [hnil]
      rfl
  have hZparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ n ∈ q.lps, ψ₁ n = ψ₂ n) →
      (∀ c, uOf c ψ₁ = uOf c ψ₂) ∧
      (fun c => dZ.Fss c ψ₁) = (fun c => dZ.Fss c ψ₂) ∧
      (∀ c, dZ.Ess c ψ₁ = dZ.Ess c ψ₂) := by
    intro ψ₁ ψ₂ hφ
    refine ⟨fun c => hUparams c ψ₁ ψ₂ hφ, funext fun c => ?_, fun c => ?_⟩
    · show fssOfR _ _ = fssOfR _ _; rw [hcdsParams c ψ₁ ψ₂ hφ]
    · show essOfR _ = essOfR _; rw [hcdsParams c ψ₁ ψ₂ hφ]
  -- ## the HOLE chains: the formers' leaves are the
  -- block operator at the constructors' fields with holes, graded by U2
  -- (the positivity stage's run) at the dummy carrier
  have hk0 : 0 < q.k := hne
  have hnilCtors : ∀ c : Nat, ¬ c < q.k → q.memberCtors.getD c [] = [] :=
    fun c hc => getD_of_le [] (by rw [hlenCtorsAs]; omega)
  have hctorLt : ∀ (c j : Nat) (cA : ConstantVal × Nat),
      (q.memberCtors.getD c [])[j]? = some cA → c < q.k := by
    intro c j cA hj
    by_cases hc : c < q.k
    · exact hc
    · rw [hnilCtors c hc] at hj; exact nomatch hj
  have hNZ : BlockNamesOk (V := V) dZ q.formers :=
    ⟨fun c cvTb hc => (hF.nameOf c cvTb hc).symm,
      fun c j cA hj => by rw [hF.lenCv]; exact hctorLt c j cA hj, hF.lenCv⟩
  have hclosedZ : ∀ (c j : Nat) (cA : ConstantVal × Nat), (dZ.ctorsM c)[j]? = some cA →
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true := by
    intro c j cA hj
    have hck := hctorLt c j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf c hck
    obtain ⟨c', sorts, -, -, -, -, -, -, -, -, -, -, hCtor⟩ := (hfacts c cvTa hck hcv).2 j cA hj
    obtain ⟨hf, -, -, hb, -⟩ := ConLeche.direct_sum_ctor_typeWF hCtor
    exact ⟨hf, hb⟩
  have hlpsZ : ∀ (c j : Nat) (cA : ConstantVal × Nat), (dZ.ctorsM c)[j]? = some cA →
      cA.1.levelParams = q.lps := by
    intro c j cA hj
    have hck := hctorLt c j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf c hck
    obtain ⟨c', sorts, -, -, -, hl, -⟩ := (hfacts c cvTa hck hcv).2 j cA hj
    exact hl
  have hlenP0 : ∀ (ψ : Name → Nat) (mm : Nat), mm < q.k →
      (((ppsOf mm ψ).take q.nP)).length = q.nP := by
    intro ψ mm hmm
    rw [List.length_take, hlenPpsOf mm hmm ψ]
    omega
  -- the members' formers, as the stored field shape facts' producer reads them
  have hformersI : ∀ t, t < q.k → ∃ cv caps,
      envI.find? (q.memberNames.getD t .anonymous) = some (.indInfo cv caps) ∧
      cv.levelParams = q.lps := by
    intro t ht
    obtain ⟨cvTb, hcv⟩ := hcvOf t ht
    obtain ⟨cvS, hfS, hDS⟩ := (hfindD t cvTb hcv).1
    refine ⟨cvS, ConLeche.blockCapsAt q t isRec, ?_, hDS.lps.trans (hF.lpsOf t cvTb hcv)⟩
    rw [← hF.nameOf t cvTb hcv]
    exact hfS
  have hTasI : ∀ cvT ∈ q.formers, cvT.type.hasFvar = false := by
    exact formers_closed hfindD
  have hgetCA : ∀ (c j : Nat) (cA : ConstantVal × Nat), (q.memberCtors.getD c [])[j]? = some cA →
      (q.memberCtors.getD c []).getD j default = cA := fun c j cA hj => by
    rw [List.getD_eq_getElem?_getD, hj]; rfl
  -- the datum's normal forms are the run's, at every stored constructor
  have hnfZ : ∀ (c j : Nat) (cA : ConstantVal × Nat), (dZ.ctorsM c)[j]? = some cA →
      dZ.nfFF c j = (posKs.2.1.getD c []).getD j default := by
    intro c j cA hj
    show (pk₀ c).nf j = _
    rw [hnf₀, ite_eq_left (show j < (q.memberCtors.getD c []).length from (List.getElem?_eq_some_iff.mp hj).1)]
  have hFZ : ∀ (c : Nat) (cvTb : ConstantVal), q.formers[c]? = some cvTb →
      FormerStored mpD.base2 cvTb (ConLeche.blockCapsAt q c isRec) ∧
      FormerData mpD.base2 cvTb (dZ.nP + dZ.nIdxAt c) dZ.resSort (dZ.ppsM c) :=
    fun c cvTb hc => ⟨(hfindD c cvTb hc).1, hFDD c cvTb hc⟩
  -- every member's parameter telescope is satisfied where the block's is
  have hparsTZ : ∀ t, t < dZ.k → ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat V (dZ.params ψ).reverse ρ →
      Sat V (((dZ.ppsM t ψ).take dZ.nP)).reverse ρ :=
    fun t ht ψ ρ h => (hF.paramsIff 0 t hk0 ht ψ ρ).mp h
  -- the fields with holes ARE the normal form's reading, at the dummy carrier
  have hAbsZ : ∀ (c j : Nat) (cA : ConstantVal × Nat), (dZ.ctorsM c)[j]? = some cA →
      BlockAbsRead mpD.base2 dZ q.lps c j cA := by
    intro c j cA hj
    have hck := hctorLt c j cA hj
    obtain ⟨hCf, hCb⟩ := hclosedZ c j cA hj
    refine blockAbsRead_of_run mpD hNZ hFZ hPos rfl rfl rfl rfl rfl hlenN.symm hndM
      (fun c hc => hCA c hc) hlenCtorsAs hclosedZ hlpsZ hparsTZ hformersI hck hj
      ((hpk₀ c hck j cA hj).storedCtorFacts hCf hCb) (hnfZ c j cA hj) (fun ψ => ?_)
    show (pk₀ c).absF j ψ = _
    rw [habs₀, hgetCA c j cA hj]
    rfl
  -- ## the walk's environment copies no member out (`WhnfNamesFree`):
  -- the members are fresh formers over the pre-block environment
  have hmemName : ∀ t, t < q.k → q.memberNames.getD t .anonymous ∈ q.memberNames := fun t ht =>
    getD_mem _ (by rw [hlenN]; exact ht)
  have hnamesIff : ∀ n, n ∈ q.memberNames ↔ ∃ cvTb ∈ q.formers, cvTb.name = n := fun n =>
    ⟨fun hn => by
        obtain ⟨t, ht⟩ := List.getElem?_of_mem hn
        have htk : t < q.k := by
          have := (List.getElem?_eq_some_iff.mp ht).1; rw [hlenN] at this; exact this
        obtain ⟨cvTb, hcv⟩ := hcvOf t htk
        refine ⟨cvTb, List.mem_of_getElem? hcv, ?_⟩
        rw [hF.nameOf t cvTb hcv, List.getD_eq_getElem?_getD, ht]; rfl,
      fun ⟨cvTb, hcvTb, hh⟩ => by
        obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
        have htk : t < q.k := by
          have := (List.getElem?_eq_some_iff.mp ht).1; rwa [hF.lenCv] at this
        rw [← hh, hF.nameOf t cvTb ht]; exact hmemName t htk⟩
  have hfindMI : ∀ cvTb ∈ q.formers, ∃ cvS caps, envI.find? cvTb.name = some (.indInfo cvS caps) ∧
      (ConLeche.declinedAtDefinition.contains cvTb.name = true →
        ∃ k bs s, cvS.type.stripPis k = some (bs, .sort s)) := fun cvTb hcvTb => by
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
    obtain ⟨bs, hbs⟩ := hF.stripOf t cvTb ht
    obtain ⟨cvS, hfS, hDS⟩ := (hfindD t cvTb ht).1
    refine ⟨cvS, _, hfS, fun hg => ?_⟩
    rcases hDS.shows with ⟨-, hgS⟩ | rfl
    · rw [hDS.name, hg] at hgS; exact nomatch hgS
    · exact ⟨_, bs, _, hbs⟩
  have hfreshI : ∀ cvTb ∈ q.formers, env.find? cvTb.name = none := fun cvTb hcvTb => by
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
    exact hF.freshOf t cvTb ht
  have hII : ∀ n, (∀ cvTb ∈ q.formers, cvTb.name ≠ n) → envI.find? n = env.find? n :=
    fun n hn => by
      rw [hcons]
      refine consBlockInds_find?_of_ne fun cvS hS => ?_
      obtain ⟨cvTb, hb, hnm⟩ := hofDcl cvS hS
      rw [hnm]
      exact hn cvTb hb
  have hWI : ConLeche.WhnfNamesFree envI q.memberNames := by
    refine ConLeche.whnfNamesFree_formers mp.base2.wf hnamesIff hfindMI hfreshI hII
      (by rw [hcons]; exact consBlockInds_tables _ 0 env) hboolM fun n c hc => ?_
    by_cases hn : ∀ cvTb ∈ q.formers, cvTb.name ≠ n
    · rw [hII n hn] at hc
      exact mp.base2.wf.shapes c (ConLeche.Env.find?_mem hc)
    · obtain ⟨cvTb, hcvTb, rfl⟩ : ∃ cvTb ∈ q.formers, cvTb.name = n := by
        simpa using hn
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
      obtain ⟨cvS, hfS, hDS⟩ := (hfindD t cvTb ht).1
      rw [hfS] at hc
      obtain rfl := Option.some.inj hc
      exact hDS.shape _ rfl
  -- the formers' types resolve before the block: they name no member
  have hTyI : ∀ (c : Nat) (cvTb : ConstantVal), q.formers[c]? = some cvTb →
      cvTb.type.occDeep q.memberNames = false := fun c cvTb hcv =>
    ConLeche.Expr.occDeep_of_constsResolve (fun n hn => hnamesFresh n hn)
      _ (hF.resolveOf c cvTb hcv)
  -- the normal forms' own facts: member-free, at the block's levels
  have hnfFacts : ∀ (c j : Nat) (cA : ConstantVal × Nat), (dZ.ctorsM c)[j]? = some cA →
      (dZ.nfFF c j).nestOcc q.memberNames 0 0 = false ∧ lpDefF q.lps (dZ.nfFF c j) = true := by
    intro c j cA hj
    have hck := hctorLt c j cA hj
    obtain ⟨hCf, hCb⟩ := hclosedZ c j cA hj
    obtain ⟨-, hlp, -⟩ := blockRunLink mpD hNZ hFZ hPos rfl rfl rfl rfl rfl hlenN.symm hndM
      (fun c hc => hCA c hc) hlenCtorsAs hclosedZ hlpsZ hparsTZ (fun _ => 0) hformersI hck hj
      ((hpk₀ c hck j cA hj).storedCtorFacts hCf hCb)
    rw [hnfZ c j cA hj]
    exact ⟨blockRunNf_nestOcc mpD hFZ hPos rfl rfl rfl
      (fun c hc => hCA c hc) hlenCtorsAs hclosedZ hlpsZ hWI hTyI hck hj, hlp⟩
  have hctxZ : BlockHoleCtxFacts mpD.base2 dZ q.lps q.formers q isRec :=
    ⟨fun c cvTb hc => ⟨(hfindD c cvTb hc).1, hFDD c cvTb hc⟩,
      fun c j cA hj => ⟨hpk₀ c (hctorLt c j cA hj) j cA hj, hAbsZ c j cA hj⟩, hlpsZ, hparsTZ⟩
  have hHZ : BlockHoleFacts mpD.base2 dZ q.lps := by
    refine ⟨fun c _ j cA hj => hpk₀ c (hctorLt c j cA hj) j cA hj,
      fun ψ c hc j hj => (blockStoredShapes_of_run mpD hNZ hctxZ hPos rfl rfl rfl rfl rfl
        hlenN.symm hndM rfl (fun c hc => hCA c hc) hlenCtorsAs hclosedZ hnfZ ψ hformersI hc
        hj),
      fun ψ => hlenP0 ψ 0 hk0, fun ψ mm hmm => hlenP0 ψ mm hmm,
      fun ψ mm hmm ρ h => (hF.paramsIff 0 mm hk0 hmm ψ ρ).mp h,
      fun ψ mm hmm ρ h => (hF.paramsIff 0 mm hk0 hmm ψ ρ).mpr h,
      fun ψ c _ j hj => ?_⟩
    obtain ⟨cA, hjA⟩ : ∃ cA, (q.memberCtors.getD c [])[j]? = some cA :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    rw [hEssZD c j cA ψ hjA]
    show ((pk₀ c).esF j ψ).length = (((ppsOf c ψ).drop q.nP)).length
    rw [hIdsLen c ψ]
    exact (hpk₀ c (hctorLt c j cA hjA) j cA hjA).lenE ψ
  -- U2's grading, per constructor
  have hGZ := fun (ψ : Name → Nat) (c : Nat) (hc : c < dZ.N) (j : Nat)
      (hj : j < (dZ.ctorsM c).length) =>
    blockHoleGrade_of_run mpD hNZ hctxZ hPos rfl rfl rfl rfl rfl hlenN.symm rfl
      (fun c hc => hCA c hc) hlenCtorsAs hclosedZ hnfZ ψ hc hj
  -- the hole chains: graded and closed
  have hchZ := fun (ψ : Name → Nat) => blockHoleChains_facts hHZ ψ
    (fun ρp hs c hc => by
      have hck : c < q.k := by have : c < q.k + 0 := hc; omega
      obtain ⟨cvTb, hcv⟩ := hcvOf c hck
      exact hIdxOf c cvTb hcv ψ ρp (hρpOf ψ ρp 0 hk0 hs c hck))
    (fun c _ => hIdsBelow c ψ) (fun c hc j hj => hGZ ψ c hc j hj)
  -- the hole chains depend on the block's level parameters only
  have hpp : ∀ (ψ₁ ψ₂ : Name → Nat), (∀ n ∈ q.lps, ψ₁ n = ψ₂ n) → ∀ c, ppsOf c ψ₁ = ppsOf c ψ₂ := by
    intro ψ₁ ψ₂ hφ c
    cases hc : q.formers[c]? with
    | none => rw [hF.ppsNil c hc, hF.ppsNil c hc]
    | some cvTb =>
      exact ((hF.fdOf c cvTb hc).params ψ₁ ψ₂
        (fun n hn => hφ n (by rw [← hF.lpsOf c cvTb hc]; exact hn))).1
  have hlpN : ∀ c j, lpDefF q.lps ((pk₀ c).nf j) = true := by
    intro c j
    by_cases hj : j < (q.memberCtors.getD c []).length
    · exact (hnfFacts c j _ (List.getElem?_eq_getElem hj)).2
    · rw [hnf₀, ite_eq_right hj]; rfl
  have hparamsH : ∀ ψ₁ ψ₂ : Name → Nat, (∀ n ∈ q.lps, ψ₁ n = ψ₂ n) →
      dZ.toLfp.holeChains ψ₁ = dZ.toLfp.holeChains ψ₂ := by
    intro ψ₁ ψ₂ hφ
    obtain ⟨hu, hfz, hes⟩ := hZparams ψ₁ ψ₂ hφ
    refine LfpDatum.holeChains_congr rfl (fun m => hu m)
      (fun c => by
        show ((ppsOf c ψ₁).drop q.nP) = ((ppsOf c ψ₂).drop q.nP)
        rw [hpp ψ₁ ψ₂ hφ c])
      (fun _ => rfl) (fun c j => ?_) (fun c j => ?_)
    · show (pk₀ c).absF j ψ₁ = (pk₀ c).absF j ψ₂
      rw [habs₀, habs₀]
      exact nfFieldsRead_params mpD.base2 (hlpN c j) hφ
    · exact BlockData.absE_congr rfl (by rw [hes c]) (by rw [congrFun hfz c])
  -- ## the hole operator's fixed-point premises: accessible at every level, so
  -- monotone (`AccW.mono`) and with (W) (`AccW.closed`)
  have hfunZ : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (dZ.params ψ).reverse ρp →
      AccW (dZ.w ψ) dZ.k (blockIdx (fun c => dZ.uM c ψ) ρp (fun c => dZ.IdsM c ψ))
        (blockPhiG dZ.k (dZ.w ψ) ρp (fun c => dZ.uM c ψ) (fun c => dZ.IdsM c ψ)
          (dZ.toLfp.holeChains ψ)) ∧
      ∃ A, (dZ.w ψ ≠ 0 → A ∈ˢ (tg (dZ.w ψ) : V)) ∧ dZ.toLfp.FitAcc ψ ρp A := by
    intro ψ ρp hs
    have hIdxZ : ∀ c, c < dZ.N → IdxOk (dZ.uM c ψ) ρp (dZ.IdsM c ψ) := fun c hc => by
      have hck : c < q.k := by have : c < q.k + 0 := hc; omega
      exact hIdxOf c (hcvOf c hck).choose (hcvOf c hck).choose_spec ψ ρp
        (hρpOf ψ ρp 0 hk0 hs c hck)
    have hkN : dZ.toLfp.k ≤ dZ.toLfp.N := Nat.le_add_right _ _
    have hok : dZ.toLfp.HoleTmOk ψ ρp := fun m hm _ => (hIdxZ m (Nat.lt_of_lt_of_le hm hkN)).2
    have hfib : ∀ X, InTupleSpace (dZ.toLfp.w ψ) dZ.toLfp.N (dZ.toLfp.idx ψ ρp) X →
        ∀ c, c < dZ.toLfp.N → ∀ t, t ∈ˢ dZ.toLfp.idx ψ ρp c → ∀ x,
          x ∈ˢ app (dZ.toLfp.Φ ψ ρp X c) t ↔
            ∃ j fs, dZ.toLfp.HFits ψ ρp X t c j fs ∧ x = dZ.toLfp.inj ψ c j fs := by
      intro X _ c hc t ht x
      have hres : ∀ j, j < dZ.toLfp.nctors c →
          (dZ.toLfp.resIdx ψ c j).length = (dZ.toLfp.ids c ψ).length := by
        intro j hj
        show (dZ.absE ψ c j).length = (dZ.IdsM c ψ).length
        simp only [BlockData.absE, List.length_map]
        exact hHZ.lenE ψ c hc j hj
      exact LfpDatum.holeOp_fibre hok hkN X hres ht x
    -- the fit's accessibility, at every level; the operator's from it
    have hGw : ∀ c, c < dZ.N → ∀ j, j < (dZ.ctorsM c).length →
        ∀ X, InTupleSpace (dZ.toLfp.w ψ) dZ.toLfp.N (dZ.toLfp.idx ψ ρp) X →
        FieldsOkB (dZ.w ψ) (dZ.toLfp.frame ψ ρp X) (dZ.absF ψ c j) :=
      fun c hc j hj X hX => (((hGZ ψ c hc j hj).2 ρp hs X hX.toU)).1
    obtain ⟨A, hA, hfa⟩ := blockAcc_of_run mpD hNZ hctxZ hPos rfl rfl rfl rfl rfl rfl hlenN.symm
      rfl hlenCtorsAs (fun c hc => hCA c hc) hclosedZ hnfZ hcovD ψ ρp hs hGw
    exact ⟨⟨A, hA, hfa.accTuple hfib⟩, A, hA, hfa⟩
  -- a unit-like member's hole leaf folds to the one tagged empty tuple
  have hfoldZH : ∀ (j : Nat) (cvTa : ConstantVal), q.formers[j]? = some cvTa →
      (ConLeche.blockCapsAt q j isRec).unitlike = true →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
        SpineFit ρ ((ppsOf j ψ)) ts →
        ts.foldl SetTheory.app (interp V ρ
            (blockTyG q.k (q.resSort.eval ψ) (fun c => uOf c ψ)
              (fun c => ((ppsOf c ψ).drop q.nP)) (dZ.toLfp.holeChains ψ)
              (ppsOf j ψ) j))
          = sumSet (q.resSort.eval ψ) (sumFibre (q.resSort.eval ψ) (consList ts ρ)
              [[] ++ [idxEqAV []]]) := by
    intro j cvTa hcv hu ψ ρ ts hsp
    have hjk : j < q.k := by
      have := (List.getElem?_eq_some_iff.mp hcv).1; rwa [hF.lenCv] at this
    -- the member's shape: one constructor, no field, no index
    obtain ⟨c, hcs, -⟩ | hcaps := blockCapsAt_cases q j isRec
    case inr => rw [hcaps] at hu; exact nomatch hu
    have hnIdx0 : q.nIdxs.getD j 0 = 0 := by
      rw [blockNIdxs_getD (q := q) (j := j) hjk]
      exact blockCapsAt_unitlike_nIdx hu
    have hlenA : (q.memberCtors.getD j []).length = 1 := by
      rw [(hfacts j cvTa hjk hcv).1.1, hcs]; rfl
    obtain ⟨cA, hcA⟩ : ∃ cA, (q.memberCtors.getD j [])[0]? = some cA :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenA]; exact Nat.zero_lt_one)⟩
    have hzA : cA.2 = 0 := by
      obtain ⟨c', -, hc', -, hnF, -⟩ := (hfacts j cvTa hjk hcv).2 0 cA hcA
      rw [hcs] at hc'
      obtain rfl : c = c' := by simpa using hc'
      rw [hnF]
      have := blockCapsAt_unitlike hu
      rcases blockCapsAt_cases q j isRec with ⟨c₂, hcs₂, hcaps₂⟩ | hcaps₂
      · rw [hcs] at hcs₂
        obtain rfl : c = c₂ := by simpa using hcs₂
        rw [hcaps₂] at this
        exact this.1
      · rw [hcaps₂] at hu; exact nomatch hu
    have hIds0 : ((ppsOf j ψ).drop q.nP) = [] := by
      refine List.length_eq_zero_iff.mp ?_
      rw [hIdsLen j ψ, hnIdx0]
    have hFss0 : dZ.Fss j ψ = [[]] := by
      obtain ⟨Fs, hFs⟩ := List.length_eq_one_iff.mp (by rw [hlenFssZ j ψ, hlenA] :
        (dZ.Fss j ψ).length = 1)
      have hl := hlenFsZ j 0 cA ψ hjk hcA
      rw [hFs, hzA] at hl
      simp only [List.getD_cons_zero] at hl
      rw [hFs, List.length_eq_zero_iff.mp hl]
    have hEss0 : dZ.Ess j ψ = [[]] := by
      obtain ⟨Es, hEs⟩ := List.length_eq_one_iff.mp (by
        rw [hlenEssZ j ψ, hlenA] : (dZ.Ess j ψ).length = 1)
      have hE0 : Es = (pk₀ j).esF 0 ψ := by
        have h := hEssZD j 0 cA ψ hcA
        rwa [hEs] at h
      have hlen : ((pk₀ j).esF 0 ψ).length = 0 := by
        have h := (hpk₀ j hjk 0 cA hcA).lenE ψ
        rwa [hnIdx0] at h
      rw [hEs, hE0, List.length_eq_zero_iff.mp hlen]
    have h := blockHoleFold_params (d := dZ) (A := blockLeafH dZ) hHZ rfl (fun _ _ => rfl)
      (fun c hc => by
        show (ppsOf c ψ).length = q.nP + (((ppsOf c ψ).drop q.nP)).length
        rw [hIdsLen c ψ]; exact hlenPpsOf c hc ψ)
      hjk hIds0
      (fun ρp hs => fun c hc => hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
        (hρpOf ψ ρp 0 hk0 hs c hc))
      (fun ρp hs => (hchZ ψ).1 ρp hs) (fun ρp hs => (hfunZ ψ ρp hs).1)
      (fun ρp _ j' hj' i hi => by
        rw [hFss0] at hi
        have : j' = 0 := by
          have : j' < (q.memberCtors.getD j []).length := hj'
          omega
        subst this
        exact absurd hi (Nat.not_lt_zero _))
      hsp
    rw [hFss0, hEss0, rChains_single_nil] at h
    exact h
  -- ## the REAL pass: the k formers at the HOLE leaves
  obtain ⟨mpR, hEclR, hFDR, hdclR, hfindR₀, hagR⟩ :=
    blockRealPass (uOf := uOf) (Chs := fun ψ => dZ.toLfp.holeChains ψ)
      mp hInd hF hndM hE hetaNe hetaFresh hIdsLen hIdsBelow
      (fun ψ c hc => (hchZ ψ).2 c hc)
      (fun ψ₁ ψ₂ hφ => ⟨(hZparams ψ₁ ψ₂ hφ).1, hparamsH ψ₁ ψ₂ hφ⟩)
      (fun j hj ψ ρp hρp c hc => hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
          (hρpOf ψ ρp j hj hρp c hc))
      (fun j hj ψ ρp hρp => (hchZ ψ).1 ρp (hρpOf ψ ρp j hj hρp 0 hk0))
      hfoldZH
  have hfindR := formerStored_of hF.lenDcl hdclR hfindR₀
  -- ## the constructors, read again at the REAL carrier
  obtain ⟨pk, hpk, habsR⟩ : ∃ pk : Nat → BlockMemberPick, (∀ m : Nat, m < q.k →
      ∀ (j : Nat) (cA : ConstantVal × Nat), (q.memberCtors.getD m [])[j]? = some cA →
        BlockCtorDataI mpR.base2 (q.memberNames.getD m .anonymous)
          q.lps cA.1 q.nP cA.2 (q.nIdxs.getD m 0) q.resSort q.isProp q.large
          ((pk m).idxF j) ((pk m).dsF j) ((pk m).esF j) ((pk m).srcsF j)
          ((pk m).fvsPF j) ((pk m).xFvsF j) ((pk m).xrestF j)) ∧
      -- the fields with holes and the normal forms: the dummy datum's, shared
      ∀ m, (pk m).absF = (pk₀ m).absF ∧ (pk m).nf = (pk₀ m).nf :=
    ⟨fun m => { (hpickOf mpR (fun j cvTb hj => (hfindR j cvTb hj).1) m).choose with
        absF := (pk₀ m).absF, nf := (pk₀ m).nf },
      fun m => (hpickOf mpR (fun j cvTb hj => (hfindR j cvTb hj).1) m).choose_spec,
      fun _ => ⟨rfl, rfl⟩⟩
  have hEssRD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (q.memberCtors.getD m [])[j]? = some cA →
      ((blockDataOf V q pk uOf ppsOf).Ess m ψ).getD j [] = (pk m).esF j ψ :=
    fun _ _ _ _ hj => essOfR_fixCtorDataList_getD hj
  -- ## the fields with holes are the walked term's reading at the REAL
  -- carrier too: it agrees with the dummy one off the members, and the
  -- walked term looks up no member (M2′, `nfFieldsRead_agree`)
  have hagDR : ∀ n, n ∉ q.memberNames → mpD.base2.acval n = mpR.base2.acval n := by
    intro n hn
    have hne' : ∀ cvTb ∈ q.formers, n ≠ cvTb.name := by
      intro cvTb hcvTb hh
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
      have htk : t < q.k := by
        have := (List.getElem?_eq_some_iff.mp ht).1; rwa [hF.lenCv] at this
      exact hn (by rw [hh, hF.nameOf t cvTb ht]; exact hmemName t htk)
    rw [hagR n hne', hagD n hne']
  have hlitI := blockMembers_notLit mp.base2.wf (cvTas := q.formers) (names := q.memberNames)
    (envI := envI) hnamesIff hfindMI hfreshI hII
  have hoccI := canonOcc_of_positivity hPos (d := dZ) rfl rfl rfl (fun c hc => hCA c hc) hlpsZ
  have hAbsR : ∀ (c j : Nat) (cA : ConstantVal × Nat),
      ((blockDataOf V q pk uOf ppsOf).ctorsM c)[j]? = some cA →
      BlockAbsRead mpR.base2 (blockDataOf V q pk uOf ppsOf) q.lps c j cA := by
    intro c j cA hj
    have hck := hctorLt c j cA hj
    obtain ⟨hCf, hCb⟩ := hclosedZ c j cA hj
    refine blockAbsRead_of_run (d := blockDataOf V q pk uOf ppsOf) mpR hNZ
      (fun c cvTb hc => ⟨(hfindR c cvTb hc).1, hFDR c cvTb hc⟩)
      hPos rfl rfl rfl rfl rfl hlenN.symm hndM
      (fun c hc => hCA c hc) hlenCtorsAs hclosedZ (fun c j cA hj => hlpsZ c j cA hj)
      (fun t ht ψ ρ h => (hF.paramsIff 0 t hk0 ht ψ ρ).mp h) hformersI
      hck hj ((hpk c hck j cA hj).storedCtorFacts hCf hCb)
      (by show (pk c).nf j = _; rw [(habsR c).2]; exact hnfZ c j cA hj) (fun ψ => ?_)
    show (pk c).absF j ψ = _
    rw [(habsR c).1, habs₀, hgetCA c j cA hj]
    show _ = nfFieldsRead _ _ _ _ ((pk c).nf j) ψ
    rw [(habsR c).2]
    exact nfFieldsRead_agree hagDR (hnfFacts c j cA hj).1 hlitI.1 hlitI.2 ψ
  -- the result index readings with holes agree too: the two carriers
  -- read the canonical crest alike
  have hAbsE : ∀ (c j : Nat) (cA : ConstantVal × Nat), (q.memberCtors.getD c [])[j]? = some cA →
      ∀ ψ : Name → Nat, (blockDataOf V q pk uOf ppsOf).absE ψ c j = dZ.absE ψ c j := by
    intro c j cA hj ψ
    have hck := hctorLt c j cA hj
    obtain ⟨-, A, hA, hr⟩ := hAbsZ c j cA hj
    obtain ⟨-, A', hA', hr'⟩ := hAbsR c j cA hj
    obtain rfl : A = A' := Option.some.inj (hA.symm.trans hA')
    obtain ⟨ab, -, hab, -, hlab, -⟩ := hr ψ
    obtain ⟨ab', -, hab', -, hlab', -⟩ := hr' ψ
    have e1 : denote mpD.base2.acval envI ψ (q.nP + q.k) A
        = some (mkPisAV ab (Term.mkAppN (.bvar (cA.2 + (q.k - 1 - c)))
            (dZ.absE ψ c j))) := hab
    have e2 : denote mpR.base2.acval envI ψ (q.nP + q.k) A
        = some (mkPisAV ab' (Term.mkAppN (.bvar (cA.2 + (q.k - 1 - c)))
            ((blockDataOf V q pk uOf ppsOf).absE ψ c j))) := hab'
    obtain ⟨A'', hA'', hocc''⟩ := hoccI c hck j cA hj
    rw [hA] at hA''
    obtain rfl := Option.some.inj hA''
    rw [← canonCrest_read_agree hagDR hocc'' hlitI.1 hlitI.2 ψ, e1] at e2
    obtain ⟨-, hX⟩ := mkPisAV_inj (hlab.trans hlab'.symm) (Option.some.inj e2)
    have hl : (dZ.absE ψ c j).length
        = ((blockDataOf V q pk uOf ppsOf).absE ψ c j).length := by
      simp only [BlockData.absE, List.length_map]
      rw [hEssZD c j cA ψ hj, hEssRD c j cA ψ hj, (hpk₀ c hck j cA hj).lenE ψ,
        (hpk c hck j cA hj).lenE ψ]
    exact (Term.mkAppN_inj hX hl).2.symm
  have hresIm : ∀ e : Expr, e.constsResolve env = true → e.constsResolve envI = true := by
    intro e he
    rw [hcons]
    exact consBlockInds_constsResolve _ _ _ e he
  -- ## the REAL record's own readings, and the chain facts at them
  have hleafOfR : ∀ (t : Nat), t < q.k → ∀ ψ : Name → Nat, ∃ B,
      mpR.base2.acval (q.memberNames.getD t .anonymous) ψ
        = mkLamsAV (ppsOf t ψ) B := by
    intro t ht ψ
    obtain ⟨cvTb, hcv⟩ := hcvOf t ht
    rw [← hF.nameOf t cvTb hcv, (hfindR t cvTb hcv).2 ψ]
    exact ⟨_, rfl⟩
  have hFssRD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (q.memberCtors.getD m [])[j]? = some cA →
      ((blockDataOf V q pk uOf ppsOf).Fss m ψ).getD j []
        = (((pk m).dsF j ψ).drop q.nP) :=
    fun _ _ _ _ hj => fssOfR_fixCtorDataList_getD hj
  -- ## the REAL record's fields with holes are the dummy one's:
  -- the two readings agree off the recursive fields
  have hholeEq : ∀ ψ : Name → Nat,
      (blockDataOf V q pk uOf ppsOf).toLfp.holeChains ψ
        = dZ.toLfp.holeChains ψ := by
    intro ψ
    have hgetNil : ∀ (L : List (List Term)) (j : Nat), L.length ≤ j → L.getD j [] = [] :=
      fun L j h => getD_of_le [] h
    have hlenEssR : ∀ m, ((blockDataOf V q pk uOf ppsOf).Ess m ψ).length
        = (q.memberCtors.getD m []).length := by
      intro m
      show (essOfR _).length = _
      rw [essOfR_length]
      exact fixCtorDataList_length _ _ _ _ _ _ _ _
    have hlenFssR : ∀ m, ((blockDataOf V q pk uOf ppsOf).Fss m ψ).length
        = (q.memberCtors.getD m []).length := by
      intro m
      show (fssOfR _ _).length = _
      rw [fssOfR_length]
      exact fixCtorDataList_length _ _ _ _ _ _ _ _
    refine LfpDatum.holeChains_congr rfl (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun c j => ?_) (fun c j => ?_)
    · -- the fields with holes: the dummy datum's, shared
      show (pk c).absF j ψ = (pk₀ c).absF j ψ
      rw [(habsR c).1]
    · by_cases hj : j < (q.memberCtors.getD c []).length
      · obtain ⟨cA, hjA⟩ : ∃ cA, (q.memberCtors.getD c [])[j]? = some cA :=
          ⟨_, List.getElem?_eq_getElem hj⟩
        exact hAbsE c j cA hjA ψ
      · refine BlockData.absE_congr rfl ?_ ?_
        · rw [hgetNil _ _ (by rw [hlenEssR c]; omega), hgetNil _ _ (by rw [hlenEssZ c ψ]; omega)]
        · rw [hgetNil _ _ (by rw [hlenFssR c]; omega), hgetNil _ _ (by rw [hlenFssZ c ψ]; omega)]
  -- ## the constructors' frames at the real carrier
  have hframes : ∀ (m : Nat), m < q.k → ∀ (j : Nat) (cA : ConstantVal × Nat),
      (q.memberCtors.getD m [])[j]? = some cA →
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsOf m ψ).take q.nP)).reverse ρ ↔
          Sat V ((((pk m).dsF j ψ).take q.nP)).reverse ρ) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V ((((pk m).dsF j ψ).take q.nP)).reverse ρ →
          FieldsOkB (q.resSort.eval ψ) ρ ((((pk m).dsF j ψ).drop q.nP)) ∧
          (q.isProp = false →
            FieldsBound (q.resSort.eval ψ) ρ ((((pk m).dsF j ψ).drop q.nP))) ∧
          (∀ bs : List V, SpineFit ρ ((((pk m).dsF j ψ).drop q.nP)) bs →
            (∀ E ∈ (pk m).esF j ψ, WellDenoted V (consList bs ρ) E) ∧
            SpineFit ρ (((ppsOf m ψ).drop q.nP))
              (idxValsAt ρ ((pk m).esF j ψ) bs))) := by
    intro m hm j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf m hm
    obtain ⟨c, sorts, -, -, -, -, -, -, -, -, -, -, hCtor⟩ := (hfacts m cvTa hm hcv).2 j cA hj
    have hTname : cvTa.name = q.memberNames.getD m .anonymous := hF.nameOf m cvTa hcv
    obtain ⟨cvS, -, hDS⟩ := (hfindR m cvTa hcv).1
    rw [hTname] at hCtor
    obtain ⟨h1, h2, -⟩ := ctorFramesGen mpR hCtor hDS.readFvar hDS.readBounded hProp' (hFDR m cvTa hcv)
      (hpk m hm j cA hj).toCtorDataI (hleafOfR m hm)
    exact ⟨h1, h2⟩
  -- ## the block's names, member by member
  have hnamesEq : ∀ (m : Nat), m < q.k →
      (q.memberCtors.getD m []).map (·.1.name)
        = (q.members.getD m default).ctors.map (·.1.name) := by
    intro m hm
    obtain ⟨cvTa, hcv⟩ := hcvOf m hm
    refine List.ext_getElem? fun i => ?_
    rw [List.getElem?_map, List.getElem?_map]
    cases hi : (q.memberCtors.getD m [])[i]? with
    | none =>
      have : (q.members.getD m default).ctors[i]? = none := by
        rw [List.getElem?_eq_none_iff] at hi ⊢
        rw [← (hfacts m cvTa hm hcv).1.1]; exact hi
      rw [this]
    | some cA =>
      obtain ⟨c, -, hc, hname, -⟩ := (hfacts m cvTa hm hcv).2 i cA hi
      rw [hc]
      simp [hname]
  have hndM' : ∀ (m : Nat), m < q.k →
      ((q.members.getD m default).ctors.map (·.1.name)).Nodup := by
    intro m hm
    refine List.Nodup.sublist (List.Sublist.map _ ?_) hndC
    show ((q.members.getD m default).ctors).Sublist ((q.members.map (·.ctors)).flatten)
    exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨_, getD_mem default hm, rfl⟩)
  have hmembersGetD : ∀ (m : Nat), m < q.k →
      q.members[m]? = some (q.members.getD m default) :=
    fun m hm => by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]; rfl
  have hmnameNe : ∀ (c m : Nat), c < q.k → m < q.k → c ≠ m →
      (q.members.getD m default).cvT.name ≠ (q.members.getD c default).cvT.name := by
    intro c m hc hm hcm
    have h := nodup_getElem_ne hndM (show m < q.memberNames.length from by rw [hlenN]; exact hm)
      (show c < q.memberNames.length from by rw [hlenN]; exact hc) (fun hh => hcm hh.symm)
    have hm' : q.memberNames[m]'(by rw [hlenN]; exact hm) = (q.members.getD m default).cvT.name := by
      have : q.memberNames[m]'(by rw [hlenN]; exact hm) = q.memberNames.getD m .anonymous := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenN]; exact hm)]
        rfl
      rw [this, ConLeche.BlockShape.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
      rfl
    have hc' : q.memberNames[c]'(by rw [hlenN]; exact hc) = (q.members.getD c default).cvT.name := by
      have : q.memberNames[c]'(by rw [hlenN]; exact hc) = q.memberNames.getD c .anonymous := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenN]; exact hc)]
        rfl
      rw [this, ConLeche.BlockShape.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
      rfl
    rw [hm', hc'] at h
    exact h
  have hmemNames : ∀ (m : Nat), m < q.k →
      (q.members.getD m default).cvT.name ∈ q.memberNames := by
    intro m hm
    show _ ∈ q.members.map _
    exact List.mem_map.mpr ⟨_, getD_mem default hm, rfl⟩
  -- ## the constructors' stage invariant at the REAL carrier
  have hcoreR : BlockCtorsCore mpR.base2 (blockDataOf V q pk uOf ppsOf)
      q.lps q.formers q isRec (blockLeafH (blockDataOf V q pk uOf ppsOf)) 0 := by
    refine ⟨fun c cvTb hc => ⟨(hfindR c cvTb hc).1, hresIm _ (hF.resolveOf c cvTb hc),
        fun ψ => by rw [(hfindR c cvTb hc).2 ψ]; unfold blockLeafH; rw [hholeEq ψ]; rfl,
        hFDR c cvTb hc⟩,
      fun c j cA hj => ?_, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
    have hck : c < q.k := hctorLt c j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf c hck
    obtain ⟨-, -, -, -, -, -, -, hres, -⟩ := (hfacts c cvTa hck hcv).2 j cA hj
    have hD := hpk c hck j cA hj
    refine ⟨hres, fun e he => ?_, hD, hAbsR c j cA hj⟩
    exact hD.idxArgs_resolve hres e he
  -- ## the k formers' leaves: closed, and the members' values at the REAL carrier
  have hacvR : ∀ c, c < q.k → ∀ ψ : Name → Nat,
      mpR.base2.acval ((blockDataOf V q pk uOf ppsOf).memberName c) ψ
        = blockLeafH (blockDataOf V q pk uOf ppsOf) c ψ := by
    intro c hc ψ
    obtain ⟨cvTb, hcvTb⟩ := hcvOf c hc
    rw [show (blockDataOf V q pk uOf ppsOf).memberName c = cvTb.name from
      (hF.nameOf c cvTb hcvTb).symm]
    exact (hcoreR.1 c cvTb hcvTb).2.2.1 ψ
  -- ## the stored field shape facts at the REAL carrier
  have hShR : ∀ (ψ : Name → Nat) (c : Nat),
      c < (blockDataOf V q pk uOf ppsOf).N → ∀ j,
      j < ((blockDataOf V q pk uOf ppsOf).ctorsM c).length →
      StoredFieldShapes V q.k q.nP (q.resSort.eval ψ) (fun t => q.nIdxs.getD t 0)
        (fun t => mpR.base2.acval (q.memberNames.getD t .anonymous) ψ)
        ((blockDataOf V q pk uOf ppsOf).params ψ).reverse
        ((blockDataOf V q pk uOf ppsOf).absF ψ c j)
        (((blockDataOf V q pk uOf ppsOf).Fss c ψ).getD j []) :=
    fun ψ c hc j hj => (blockStoredShapes_of_run (d := blockDataOf V q pk uOf ppsOf)
      mpR hNZ (hcoreR.holeCtx (fun c j cA hj => hlpsZ c j cA hj)
        (fun t ht ψ ρ h => (hF.paramsIff 0 t hk0 ht ψ ρ).mp h)) hPos rfl rfl rfl rfl rfl
      hlenN.symm hndM rfl (fun c hc => hCA c hc) hlenCtorsAs hclosedZ
      (fun c j cA hj => by show (pk c).nf j = _; rw [(habsR c).2]; exact hnfZ c j cA hj)
      ψ hformersI hc hj)
  -- ## the constructors' stage, assembled
  have hSC : BlockCtorsStage (V := V) F (blockDataOf V q pk uOf ppsOf)
      q.lps q.formers q isRec (blockLeafH (blockDataOf V q pk uOf ppsOf))
      envI q.ctorNamesAt := by
    have hmnameEq : ∀ (m : Nat) (cvTa : ConstantVal), m < q.k → q.formers[m]? = some cvTa →
        (q.members.getD m default).cvT.name = cvTa.name := by
      intro m cvTa hm hcv
      have h1 : q.memberNames.getD m .anonymous = (q.members.getD m default).cvT.name := by
        rw [ConLeche.BlockShape.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hm, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hm]
        rfl
      rw [hF.nameOf m cvTa hcv, h1]
    have hmemIdx : ∀ (m : Nat) (cA : ConstantVal × Nat), cA ∈ q.memberCtors.getD m [] →
        ∃ j, (q.memberCtors.getD m [])[j]? = some cA := fun _ _ h => List.getElem?_of_mem h
    refine
      { leaf := fun _ _ => rfl
        holeOk := fun ψ ρp hs => by
          rw [hholeEq ψ]
          exact (hchZ ψ).1 ρp hs
        holeFun := fun ψ ρp hs => by
          obtain ⟨hacc, A, hA, hfa⟩ := hfunZ ψ ρp hs
          -- the fit reads the data through the fields and result indices: shared
          -- (each reading compared at the `BlockData` level: the two `toLfp`s differ)
          have hF : ∀ c j, dZ.absF ψ c j = (blockDataOf V q pk uOf ppsOf).absF ψ c j :=
            fun c j => by
              show (pk₀ c).absF j ψ = (pk c).absF j ψ
              rw [(habsR c).1]
          refine ⟨by rw [hholeEq ψ]; exact hacc, A, hA, LfpDatum.FitAcc.congr (D := dZ.toLfp)
            (D' := (blockDataOf V q pk uOf ppsOf).toLfp)
            (show dZ.w ψ = (blockDataOf V q pk uOf ppsOf).w ψ from rfl)
            (show dZ.N = (blockDataOf V q pk uOf ppsOf).N from rfl)
            (show dZ.k = (blockDataOf V q pk uOf ppsOf).k from rfl)
            (fun m => show dZ.uM m ψ = (blockDataOf V q pk uOf ppsOf).uM m ψ from rfl)
            (fun c => show dZ.IdsM c ψ = (blockDataOf V q pk uOf ppsOf).IdsM c ψ from rfl)
            (fun c => show (dZ.ctorsM c).length
              = ((blockDataOf V q pk uOf ppsOf).ctorsM c).length from rfl)
            (fun c j _ => show dZ.absF ψ c j = _ from hF c j)
            (fun c j hj => show dZ.absE ψ c j = _ from
              (hAbsE c j _ (List.getElem?_eq_getElem hj) ψ).symm) hfa⟩
        inst := rfl
        shapes := fun ψ c hc j hj =>
          (hShR ψ c (Nat.lt_of_lt_of_le hc (Nat.le_add_right _ _)) j hj).congr_leaf
            fun t ht => hacvR t ht ψ
        ctors := fun m cvTa hm hcv =>
          ⟨_, _, hCR m cvTa hm hcv⟩
        nodup := ?_
        out := ?_
        lpsT := fun m cvTa hm hcv => hF.lpsOf m cvTa hcv
        lpsA := ?_
        ndBlock := ?_
        paramsOf := fun m hm ψ ρp hρ c hc => hρpOf ψ ρp m hm hρ c hc
        lenPps := ?_
        lenIds := fun m hm ψ => hIdsLen m ψ
        idxOk := ?_
        frames := ?_
        shownAt := ?_
        capsU := ?_ }
    · -- nodup
      intro m hm
      show ((q.memberCtors.getD m []).map (·.1.name)).Nodup
      rw [hnamesEq m hm]
      exact hndM' m hm
    · -- out
      intro m cvTa hm hcv cA hcA T'' hT'' hne
      have hn : cA.1.name ∈ (q.members.getD m default).ctors.map (·.1.name) := by
        rw [← hnamesEq m hm]
        exact List.mem_map.mpr ⟨cA, hcA, rfl⟩
      exact ConLeche.blockCtorNames_out hndC (hmembersGetD m hm) hn T'' hT''
        (by rw [hmnameEq m cvTa hm hcv]; exact hne)
    · -- lpsA
      intro m hm cA hcA
      obtain ⟨j, hj⟩ := hmemIdx m cA hcA
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      obtain ⟨-, -, -, -, -, hlps, -⟩ := (hfacts m cvTa hm hcv).2 j cA hj
      exact hlps
    · -- ndBlock
      intro m hm c hcm j cB hj hmem
      have hck : c < q.k := hctorLt c j cB hj
      have hnc : cB.1.name ∈ (q.members.getD c default).ctors.map (·.1.name) := by
        rw [← hnamesEq c hck]
        exact List.mem_map.mpr ⟨cB, List.mem_of_getElem? hj, rfl⟩
      have hout := ConLeche.blockCtorNames_out hndC (hmembersGetD c hck) hnc
        ((q.members.getD m default).cvT.name) (hmemNames m hm) (hmnameNe c m hck hm hcm)
      refine hout ?_
      have hmm : cB.1.name ∈ (q.members.getD m default).ctors.map (·.1.name) := by
        rw [← hnamesEq m hm]; exact hmem
      obtain ⟨cB', hcB', hnameB⟩ := List.mem_map.mp hmm
      rw [← hnameB]
      exact ConLeche.BlockShape.mem_ctorNamesAt (getD_mem default hm) hcB'
    · -- lenPps
      intro c ψ hc
      show (ppsOf c ψ).length = q.nP + (((ppsOf c ψ).drop q.nP)).length
      rw [hIdsLen c ψ]
      exact hlenPpsOf c hc ψ
    · -- idxOk
      intro m hm ψ ρp hρp c hc
      exact hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
        (hρpOf ψ ρp m hm hρp c hc)
    · -- frames
      intro m hm j cA hj
      exact ⟨(hframes m hm j cA hj).1, fun ψ ρ hρ =>
        ⟨((hframes m hm j cA hj).2 ψ ρ hρ).1,
          fun bs hbs => (((hframes m hm j cA hj).2 ψ ρ hρ).2.2 bs hbs).2⟩⟩
    · -- the telescopes the check read
      intro m cvTa hcv
      show q.members[m]?.map (·.cvT) = some cvTa
      rw [← List.getElem?_map, hmcv, hcv]
    · -- capsU
      intro m hm cvTa hcv env' m' kk cA hkk hu hcvC hlpsCA hreadCA hFD' hleaf' hleafC'
      have hnIdx0 : q.nIdxs.getD m 0 = 0 := by
        rw [blockNIdxs_getD (q := q) (j := m) hm]
        exact blockCapsAt_unitlike_nIdx hu
      obtain ⟨c, hcs, hcaps⟩ | hcaps := blockCapsAt_cases q m isRec
      case inr => rw [hcaps] at hu; exact nomatch hu
      have hlenA : (q.memberCtors.getD m []).length = 1 := by
        rw [(hfacts m cvTa hm hcv).1.1, hcs]; rfl
      have hkk0 : kk = 0 := by
        have hlt : kk < (q.memberCtors.getD m []).length := (List.getElem?_eq_some_iff.mp hkk).1
        omega
      subst hkk0
      obtain ⟨c', -, hc', hnameC, hnF, -⟩ := (hfacts m cvTa hm hcv).2 0 cA hkk
      rw [hcs] at hc'
      obtain rfl : c = c' := by simpa using hc'
      have hzA : cA.2 = 0 := by
        have hU := blockCapsAt_unitlike hu
        rw [hcaps] at hU
        rw [hnF]
        exact hU.1
      have hlenP : ∀ ψ : Name → Nat, (ppsOf m ψ).length = q.nP := by
        intro ψ
        have := hlenPpsOf m hm ψ
        rwa [hnIdx0, Nat.add_zero] at this
      have hlenD : ∀ ψ : Name → Nat, ((pk m).dsF 0 ψ).length = q.nP := by
        intro ψ
        have := (hpk m hm 0 cA hkk).len ψ
        rwa [hzA, Nat.add_zero] at this
      have hFss1 : ∀ ψ : Name → Nat,
          (blockDataOf V q pk uOf ppsOf).Fss m ψ = [[]] := by
        intro ψ
        have hl1 : ((blockDataOf V q pk uOf ppsOf).Fss m ψ).length
            = (q.memberCtors.getD m []).length := by
          show (fssOfR _ _).length = _
          rw [fssOfR_length]
          exact fixCtorDataList_length _ _ _ _ _ _ _ _
        obtain ⟨Fs, hFs⟩ := List.length_eq_one_iff.mp (hl1.trans hlenA)
        have h0 := hFssRD m 0 cA ψ hkk
        rw [hFs] at h0 ⊢
        simp only [List.getD_cons_zero] at h0
        rw [h0]
        have : (((pk m).dsF 0 ψ).drop q.nP) = [] := by
          refine List.length_eq_zero_iff.mp ?_
          simp [hlenD ψ]
        rw [this]
      refine blockCapsLawsAt m' (T := cvTa.name) (w := fun ψ => q.resSort.eval ψ)
        (pps := ppsOf m) (ds := (pk m).dsF 0) (L := fun ψ =>
          blockLeafH (blockDataOf V q pk uOf ppsOf) m ψ)
        (fun ψ => (hlenP ψ).symm) hleaf' (fun _ => ⟨_, rfl⟩) ?_ ?_ ?_ ?_
      · -- the fold at the fieldless shape
        intro _ ψ ρ ts hsp
        unfold blockLeafH
        rw [hholeEq ψ]
        exact hfoldZH m cvTa hcv hu ψ ρ ts hsp
      · -- the one constructor's leaf
        intro _ ψ
        have hleafCraw : m'.acval cA.1.name ψ
            = sumMkAV (q.resSort.eval ψ) 0 ((pk m).dsF 0 ψ)
                ((((pk m).dsF 0 ψ).drop q.nP))
                (uChains ((blockDataOf V q pk uOf ppsOf).Fss m ψ)) :=
          hleafC' ψ
        have hnil : (((pk m).dsF 0 ψ).drop q.nP) = [] := by
          refine List.length_eq_zero_iff.mp ?_
          simp [hlenD ψ]
        rw [hnil, hFss1 ψ] at hleafCraw
        rw [hcaps]
        show m'.acval c.1.name ψ = _
        rw [← hnameC]
        exact hleafCraw
      · -- the parameter spine fits the constructor's parameters
        intro ψ ρ as hsp
        refine (spineFit_iff_of_sat_iff (by rw [hlenP ψ, hlenD ψ])
          (fun ρ' => ?_) ρ as (by rw [hsp.length_eq])).mp hsp
        have hiff := (hframes m hm 0 cA hkk).1 ψ ρ'
        rwa [List.take_of_length_le (Nat.le_of_eq (hlenP ψ)),
          List.take_of_length_le (Nat.le_of_eq (hlenD ψ))] at hiff
      · -- the η constructor's stored type reads over the same domains
        intro _ cvC nPc nFc hfC
        rw [hcaps] at hfC
        have hfC' : env'.find? cA.1.name = some (.ctorInfo cvC nPc nFc) := by
          rw [hnameC]; exact hfC
        obtain rfl := hcvC cvC nPc nFc hfC'
        exact ⟨hlpsCA, _, hreadCA⟩
  -- ## the fields' sorts, as the constructors' run read them
  have hsortsAt : ∀ (m : Nat), m < q.k → ∀ (j : Nat) (cA : ConstantVal × Nat),
      (q.memberCtors.getD m [])[j]? = some cA →
      ∃ sorts : List Level, (sortsss.getD m [])[j]? = some sorts ∧ sorts.length = cA.2 ∧
        (∀ i, i < cA.2 → q.isProp = false →
          Level.leq (sorts.getD i .zero) q.resSort = some true) ∧
        ∀ (ψ : Name → Nat) (ρ : Nat → V),
          Sat V ((((pk m).dsF j ψ).take q.nP)).reverse ρ →
          ∀ i, i < cA.2 → ∀ as : List V,
            SpineFit ρ (((((pk m).dsF j ψ).drop q.nP)).take i) as →
            interp V (consList as ρ)
                (((((pk m).dsF j ψ).drop q.nP)).getD i default)
              ∈ˢ (univ ((sorts.getD i .zero).eval ψ) : V) := by
    intro m hm j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf m hm
    obtain ⟨c, sorts, -, -, -, -, -, -, -, hsj, -, -, hCtor⟩ := (hfacts m cvTa hm hcv).2 j cA hj
    have hTname : cvTa.name = q.memberNames.getD m .anonymous := hF.nameOf m cvTa hcv
    obtain ⟨cvS, -, hDS⟩ := (hfindR m cvTa hcv).1
    rw [hTname] at hCtor
    obtain ⟨-, -, hlenS, hleq, hsorts3⟩ := ctorFramesGen mpR hCtor hDS.readFvar hDS.readBounded hProp' (hFDR m cvTa hcv)
      (hpk m hm j cA hj).toCtorDataI (hleafOfR m hm)
    exact ⟨sorts, hsj, hlenS, hleq, fun ψ ρ hρ i hi as hsp => hsorts3 ψ ρ hρ i hi as hsp⟩
  -- the constructors' hole facts at the REAL carrier
  have hHR : BlockHoleFacts mpR.base2 (blockDataOf V q pk uOf ppsOf) q.lps := by
    refine ⟨fun c _ j cA hj => hpk c (hctorLt c j cA hj) j cA hj,
      hShR,
      fun ψ => hlenP0 ψ 0 hk0, fun ψ mm hmm => hlenP0 ψ mm hmm,
      fun ψ mm hmm ρ h => (hF.paramsIff 0 mm hk0 hmm ψ ρ).mp h,
      fun ψ mm hmm ρ h => (hF.paramsIff 0 mm hk0 hmm ψ ρ).mpr h,
      fun ψ c _ j hj => ?_⟩
    obtain ⟨cA, hjA⟩ : ∃ cA, (q.memberCtors.getD c [])[j]? = some cA :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    rw [hEssRD c j cA ψ hjA]
    show ((pk c).esF j ψ).length = (((ppsOf c ψ).drop q.nP)).length
    rw [hIdsLen c ψ]
    exact (hpk c (hctorLt c j cA hjA) j cA hjA).lenE ψ
  -- ## a structure-like member's leaf folds to its one constructor's fibre
  have hfoldT : ∀ (m : Nat) (cA : ConstantVal × Nat), m < q.k → q.memberCtors.getD m [] = [cA] →
      q.nIdxs.getD m 0 = 0 →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
        SpineFit ρ ((ppsOf m ψ)) ts →
        ts.foldl SetTheory.app (interp V ρ
            (blockLeafH (blockDataOf V q pk uOf ppsOf) m ψ))
          = sumSet (q.resSort.eval ψ) (sumFibre (q.resSort.eval ψ) (consList ts ρ)
              [((((pk m).dsF 0 ψ).drop q.nP)) ++ [idxEqAV []]]) := by
    intro m cA hm hcs hnIdx0 ψ ρ ts hsp
    have hcA : (q.memberCtors.getD m [])[0]? = some cA := by rw [hcs]; rfl
    have hlenA : (q.memberCtors.getD m []).length = 1 := by rw [hcs]; rfl
    have hIds0 : ((ppsOf m ψ).drop q.nP) = [] := by
      refine List.length_eq_zero_iff.mp ?_
      rw [hIdsLen m ψ, hnIdx0]
    have hEss0 : (blockDataOf V q pk uOf ppsOf).Ess m ψ = [[]] := by
      obtain ⟨Es, hEs⟩ := List.length_eq_one_iff.mp (by
        show (essOfR _).length = 1
        rw [essOfR_length]
        exact (fixCtorDataList_length _ _ _ _ _ _ _ _).trans hlenA :
          ((blockDataOf V q pk uOf ppsOf).Ess m ψ).length = 1)
      have hE0 : Es = (pk m).esF 0 ψ := by
        have h := hEssRD m 0 cA ψ hcA
        rwa [hEs] at h
      have hlen0 : ((pk m).esF 0 ψ).length = 0 := by
        have h := (hpk m hm 0 cA hcA).lenE ψ
        rwa [hnIdx0] at h
      rw [hEs, hE0, List.length_eq_zero_iff.mp hlen0]
    have hFss1 : (blockDataOf V q pk uOf ppsOf).Fss m ψ
        = [((((pk m).dsF 0 ψ).drop q.nP))] := by
      obtain ⟨Fs, hFs⟩ := List.length_eq_one_iff.mp (by
        show (fssOfR _ _).length = 1
        rw [fssOfR_length]
        exact (fixCtorDataList_length _ _ _ _ _ _ _ _).trans hlenA :
          ((blockDataOf V q pk uOf ppsOf).Fss m ψ).length = 1)
      have h0 := hFssRD m 0 cA ψ hcA
      rw [hFs] at h0 ⊢
      simp only [List.getD_cons_zero] at h0
      rw [h0]
    have h := blockHoleFold_params (A := blockLeafH (blockDataOf V q pk uOf ppsOf))
      hHR rfl (ψ := ψ) (fun _ _ => rfl) (fun c hc => hSC.lenPps c ψ hc) hm hIds0
      (fun ρp hs => fun c hc => hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
        (hρpOf ψ ρp 0 hk0 hs c hc))
      (fun ρp hs => hSC.holeOk ψ ρp hs) (fun ρp hs => (hSC.holeFun ψ ρp hs).1)
      (fun ρp hsρ j' hj' => blockOverride hHR (fun t ht => hacvR t ht ψ) ρp hsρ
        (Nat.lt_of_lt_of_le hm (Nat.le_add_right _ _)) hj')
      hsp
    rw [hFss1, hEss0, rChains_single_nil] at h
    exact h
  refine ⟨pk, uOf, ppsOf, mpR, ?_, ?_, hcoreR, ?_, ?_,
    fun c j cA hj => by show (pk c).nf j = _; rw [(habsR c).2]; exact hnfZ c j cA hj, hagR⟩
  · -- BlockNamesOk
    exact ⟨fun c cvTb hc => (hF.nameOf c cvTb hc).symm,
      fun c j cA hj => by rw [hF.lenCv]; exact hctorLt c j cA hj, hF.lenCv⟩
  · -- BlockCtorsStage
    refine
      { toBlockCtorsStage := hSC
        etaData := ?_
        stripC := ?_
        propFlag := hProp
        propZ := fun hp m cvTa hcv s hs => by
          obtain ⟨bs, hst⟩ := hF.stripOf m cvTa hcv
          have hsS : s = sOf m := by
            unfold ConLeche.formerResSort at hs
            rw [ConLeche.piResult_of_stripPis_sort _ hst] at hs
            exact (Option.some.inj hs).symm
          subst hsS
          refine ConLeche.Level.isAlwaysZero_of_eval fun ψ => ?_
          rw [hF.sEval m ψ]
          have hp' : q.isProp = true := hp
          rw [hProp] at hp'
          exact ConLeche.Level.isEquiv_sound (beq_iff_eq.mp hp') ψ
        capsTele := fun m hm => by
          rw [blockCapsAt_telescope]
          congr 1
          show (q.members.map (·.nIdx)).getD m 0 = _
          have hmk : m < q.members.length := hm
          simp [List.getD_eq_getElem?_getD, hmk]
        resT := ?_
        resR := ?_
        resC := ?_
        leqF := ?_
        boundF := ?_
        dsLen := ?_
        dsBelow := ?_
        foldT := ?_
        sortsF := ?_ }
    · -- etaData
      intro m cA hm hcs he
      have hcs' : q.memberCtors.getD m [] = [cA] := hcs
      have hcA : (q.memberCtors.getD m [])[0]? = some cA := by rw [hcs']; rfl
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      obtain ⟨c, hcsM, hcaps⟩ | hcaps := blockCapsAt_cases q m isRec
      case inr => rw [hcaps] at he; exact nomatch he
      obtain ⟨c', -, hc0, hname, hnF, -⟩ := (hfacts m cvTa hm hcv).2 0 cA hcA
      rw [hcsM] at hc0
      obtain rfl : c = c' := by simpa using hc0
      rw [hcaps]
      exact ⟨hname.symm, rfl, hnF.symm⟩
    · -- stripC
      intro m cA hm hcs
      have hcs' : q.memberCtors.getD m [] = [cA] := hcs
      have hcA : (q.memberCtors.getD m [])[0]? = some cA := by rw [hcs']; rfl
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hstrip, -⟩ := (hfacts m cvTa hm hcv).2 0 cA hcA
      exact hstrip
    · -- resT
      intro m hm
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      rw [show (blockDataOf V q pk uOf ppsOf).memberName m = cvTa.name from
        (hF.nameOf m cvTa hcv).symm]
      exact hF.nresOf m cvTa hcv
    · -- resR: a member's recursor name is reserved only if the member's is
      intro m hm
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      rw [show (blockDataOf V q pk uOf ppsOf).memberName m = cvTa.name from
        (hF.nameOf m cvTa hcv).symm]
      exact reservedBasisNames_str_rec (hF.nresOf m cvTa hcv)
    · -- resC
      intro m cA hm hcs
      have hcs' : q.memberCtors.getD m [] = [cA] := hcs
      have hcA : (q.memberCtors.getD m [])[0]? = some cA := by rw [hcs']; rfl
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      obtain ⟨-, -, -, -, -, -, -, -, hres, -⟩ := (hfacts m cvTa hm hcv).2 0 cA hcA
      exact hres
    · -- leqF
      intro m cA hm hcs i hi hnp
      have hcs' : q.memberCtors.getD m [] = [cA] := hcs
      have hcA : (q.memberCtors.getD m [])[0]? = some cA := by rw [hcs']; rfl
      obtain ⟨sorts, hsj, -, hleq, -⟩ := hsortsAt m hm 0 cA hcA
      rw [show (sortsss.getD m []).getD 0 [] = sorts from by
        rw [List.getD_eq_getElem?_getD, hsj]; rfl]
      exact hleq i hi hnp
    · -- boundF
      intro m cA hm hcs ψ ρ hρ hnp
      have hcs' : q.memberCtors.getD m [] = [cA] := hcs
      have hcA : (q.memberCtors.getD m [])[0]? = some cA := by rw [hcs']; rfl
      exact ((hframes m hm 0 cA hcA).2 ψ ρ hρ).2.1 hnp
    · -- dsLen
      intro m j cA hm hj ψ
      exact (hpk m hm j cA hj).len ψ
    · -- dsBelow
      intro m j cA hm hj ψ
      exact (hpk m hm j cA hj).below ψ
    · -- foldT
      intro m cA hm hcs hnIdx0 ψ ρ ts hsp
      exact hfoldT m cA hm hcs hnIdx0 ψ ρ ts hsp
    · -- sortsF
      intro m cA hm hcs ψ ρ hρ j hj as hsp
      have hcs' : q.memberCtors.getD m [] = [cA] := hcs
      have hcA : (q.memberCtors.getD m [])[0]? = some cA := by rw [hcs']; rfl
      obtain ⟨sorts, hsj, -, -, hsf⟩ := hsortsAt m hm 0 cA hcA
      rw [show (sortsss.getD m []).getD 0 [] = sorts from by
        rw [List.getD_eq_getElem?_getD, hsj]; rfl]
      exact hsf ψ ρ hρ j hj as hsp
  · -- the block's η invariant at the formers' environment
    refine ⟨hEclR, ?_⟩
    rw [hcons]
    refine ConLeche.blockEtaInv_snd_consBlockInds (fun T' hT' => ?_) (fun j cvTa hj => ?_)
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hT'
      obtain ⟨cvTb, hcv⟩ : ∃ cvTb, q.formers[j]? = some cvTb :=
        ⟨_, List.getElem?_eq_getElem (by
          have hlt := (List.getElem?_eq_some_iff.mp hj).1
          rw [hlenN] at hlt
          rw [hF.lenCv]
          exact hlt)⟩
      have hname : cvTb.name = T' := by
        rw [hF.nameOf j cvTb hcv, List.getD_eq_getElem?_getD, hj]; rfl
      rw [← hname]
      exact hF.freshOf j cvTb hcv
    · have hjk : j < q.members.length := by
        have := (List.getElem?_eq_some_iff.mp hj).1
        rw [List.length_map] at this
        rw [hqm]; exact this
      refine ⟨q.members[j], List.getElem?_eq_getElem hjk, ?_⟩
      obtain ⟨cvTb, hcv⟩ : ∃ cvTb, q.formers[j]? = some cvTb :=
        ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact hjk)⟩
      rw [(hF.declOf j cvTa cvTb hj hcv).name, hF.nameOf j cvTb hcv,
        ConLeche.BlockShape.memberNames, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_getElem hjk]
      rfl
  · -- every member's constructors are fresh at the formers' environment
    intro c j cA hj
    have hck : c < q.k := hctorLt c j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf c hck
    obtain ⟨-, -, -, -, -, -, hfresh, -⟩ := (hfacts c cvTa hck hcv).2 j cA hj
    exact hfresh


end ConLeche.Model
