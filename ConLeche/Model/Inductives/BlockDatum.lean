module

public import ConLeche.Model.Inductives.BlockAssembly
public import ConLeche.Model.Inductives.BlockStageTables
import ConLeche.Model.Annot.LfpHoleOp
import ConLeche.Model.Inductives.BlockCaps
import ConLeche.Model.Inductives.BlockHoleGrade
public import ConLeche.Model.Inductives.BlockPosRunCont
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
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  BlockShape BlockParts MemberShape BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The record -/

/-- **The block's representation record but for the operator and the
injections**, at a chosen per-member constructor pick. -/
@[expose] noncomputable def blockDataPre (V : Type w) [SetTheory V] (q : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pk : Nat → BlockMemberPick)
    (uOf : Nat → (Name → Nat) → Nat)
    (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) : BlockData V where
  nP := q.nP
  k := q.k
  nInst := 0
  resSort := q.resSort
  isProp := q.isProp
  large := q.large
  memberNames := q.memberNames
  nIdxs := q.nIdxs
  ppsM := ppsOf
  uM := uOf
  ctorsM := fun c => ctorsAs.getD c []
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
    (ctorsAs : List (List (ConstantVal × Nat))) (pk : Nat → BlockMemberPick)
    (uOf : Nat → (Name → Nat) → Nat)
    (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) : BlockData V :=
  (blockDataPre V q ctorsAs pk uOf ppsOf).withPhi

/-- **A member's former leaf on the HOLE chains** (charter item 2): the block operator at the constructors' fields with
holes, the operator the datum's `Φ` IS (`BlockData.withPhi`).  It
reads no field classification and no member: the formers are consed
with it. -/
@[expose] noncomputable def blockLeafH (d : BlockData V) (c : Nat) (ψ : Name → Nat) : AnnotTerm :=
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
      ⟨.indInfo cvT (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩) = true
    exact consBlockInds_constsResolve rest (i + 1) _ e (Expr.constsResolve_mono h)

/-- **A member's recursor name is reserved only if the member's is**:
`reservedBasisNames` is five `.str _ "rec"` names and fourteen others,
none of them of that shape, so the five are the only way `T.str "rec"`
can be reserved — and then `T` is. -/
theorem reservedBasisNames_str_rec {T : Name}
    (h : ConLeche.reservedBasisNames.contains T = false) :
    ConLeche.reservedBasisNames.contains (T.str "rec") = false := by
  revert h
  simp +decide [ConLeche.reservedBasisNames, Name.str.injEq, ConLeche.eqName,
    ConLeche.eqReflName, ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName,
    ConLeche.punitName, ConLeche.punitUnitName, ConLeche.emptyName, ConLeche.falseName,
    ConLeche.quotName, ConLeche.quotMkName, ConLeche.quotLiftName, ConLeche.quotIndName,
    ConLeche.quotSoundName]
  intro h1 _ _ h4 _ _ _ h8 _ _ h11 _ h13 _ _ _ _ _ _
  exact ⟨h1, h4, h8, h11, h13⟩

/-! ## The members' constructors, as the run checked them -/

/-- **Every member's constructors, positionally** (conjunct 2 read at
one member): the stored constant's name, level parameters, field count
and freshness, and the sum route's run that produced it. -/
theorem blockCtorRuns_of {envI : Env} {q : BlockShape} {F : Nat}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {sortsss : List (List (List Level))}
    (hCtors : ConLeche.checkBlockCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI envI q
      (q.members.zip cvTas) = .ok (ctorsAs, sortsss))
    (hnameOf : ∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
      cvTb.name = q.memberNames.getD j .anonymous) :
    ∀ (m : Nat) (cvTa : ConstantVal), m < q.k → cvTas[m]? = some cvTa →
      ConLeche.checkSumCtors (ConLeche.fueledOps μ F) envI envI cvTa.name q.lps q.nP
          (q.nIdxs.getD m 0) q.resSort q.isProp q.large cvTa
          (q.members.getD m default).ctors
        = .ok (ctorsAs.getD m [], sortsss.getD m []) := by
  intro m cvTa hm hcv
  obtain ⟨-, -, hall⟩ := ConLeche.checkBlockCtors_inv hCtors
  have hml : m < q.members.length := hm
  obtain ⟨ms, hms⟩ : ∃ ms, q.members[m]? = some ms := ⟨_, List.getElem?_eq_getElem hml⟩
  obtain ⟨ctorsA, sortss, hcA, hsA, hrun⟩ := hall m (ms, cvTa) (zip_getElem? _ _ _ _ _ hms hcv)
  have hmsD : q.members.getD m default = ms := by
    rw [List.getD_eq_getElem?_getD, hms]; rfl
  have hname : ms.cvT.name = cvTa.name := by
    rw [hnameOf m cvTa hcv, BlockShape.memberNames, List.getD_eq_getElem?_getD,
      List.getElem?_map, hms]
    rfl
  have hnIdx : q.nIdxs.getD m 0 = ms.nIdx := by
    rw [BlockShape.nIdxs, List.getD_eq_getElem?_getD, List.getElem?_map, hms]; rfl
  rw [hmsD, hnIdx, ← hname, List.getD_eq_getElem?_getD, hcA, List.getD_eq_getElem?_getD, hsA]
  exact hrun

/-- **One member's constructors, as stored**: `blockCtorFuns_of`'s
`hrunOf` at a block member. -/
theorem blockCtorFacts_of {envI : Env} {q : BlockShape} {F : Nat} {cvTa : ConstantVal} {m : Nat}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hrun : ConLeche.checkSumCtors (ConLeche.fueledOps μ F) envI envI cvTa.name q.lps q.nP
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
        cA.1.name.isProjFnShape = false ∧
        ConLeche.reservedBasisNames.contains cA.1.name = false ∧
        sortss[j]? = some sorts ∧
        (cA.1.type.stripPis (q.nP + cA.2)).isSome = true ∧
        (∃ ty₀ : Expr, ty₀.hasFvar = false ∧
          ConLeche.annotateCore μ envI F 0 ty₀ = .ok cA.1.type) ∧
        ConLeche.checkSumCtor (ConLeche.fueledOps μ F) envI envI cvTa.name q.lps q.nP
          (q.nIdxs.getD m 0) q.resSort q.isProp q.large c.1 cA.2 cvTa = .ok (cA.1, sorts) := by
  obtain ⟨hlenA, hlenS, hall⟩ := ConLeche.checkSumCtors_inv hrun
  refine ⟨⟨hlenA, hlenS⟩, fun j cA hj => ?_⟩
  have hjl : j < (q.members.getD m default).ctors.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1; omega
  obtain ⟨hnF, sorts, hsj, hCtor⟩ :=
    hall j ((q.members.getD m default).ctors[j]) cA (List.getElem?_eq_getElem hjl) hj
  obtain ⟨⟨ty₀, hccvC⟩, ⟨cbs, es, hstrip, -⟩, -⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨hfindC, -, hpshapeC, -, -, hfvC, _, -, -, hannC, -, htrC, -, -, htyC⟩ :=
    ConLeche.checkConstantVal_inv hccvC
  have hmem : (q.members.getD m default).ctors[j] ∈ (q.members.getD m default).ctors :=
    List.getElem_mem hjl
  refine ⟨_, sorts, List.getElem?_eq_getElem hjl, by rw [htyC], hnF, ?_, ?_, ?_,
    by rw [htyC]; exact hpshapeC, ?_, hsj, ?_, ⟨ty₀, hfvC, ?_⟩,
    by rw [hnF]; exact hCtor⟩
  · rw [htyC]; exact (hClps _ hmem).1
  · show Env.find? _ cA.1.name = none
    rw [htyC]; exact hfindC
  · show Expr.constsResolve _ cA.1.type = true
    rw [htyC]; exact htrC
  · rw [htyC]; exact (hClps _ hmem).2
  · rw [hnF, hstrip]; rfl
  · show ConLeche.annotateCore μ envI F 0 ty₀ = .ok cA.1.type
    rw [htyC]; exact hannC

/-! ## The η side conditions of the two former passes -/

/-- A name found stays found across a cons. -/
theorem find?_isSome_consB {c : ConstantInfo} {env : Env} {n : Name}
    (h : (env.find? n).isSome = true) :
    (((⟨c :: env.consts⟩ : Env)).find? n).isSome = true := by
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
      ⟨.indInfo cvT (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩).find? n).isSome = true
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
      ⟨.indInfo cvT (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩).find? cvTa.name).isSome
      = true
    refine consBlockInds_find?_isSome_mono rest (i + 1) _ cvTa.name ?_
    have hn : (ConstantInfo.indInfo cvT (ConLeche.blockCapsAt p₁ i isRec)).name = cvT.name := rfl
    rw [← h, ← hn, ConLeche.Env.find?_cons_self]
    rfl
  | cvT :: rest, i, j + 1, env, cvTa, h => by
    simp only [List.getElem?_cons_succ] at h
    show ((ConLeche.consBlockInds p₁ isRec rest (i + 1)
      ⟨.indInfo cvT (ConLeche.blockCapsAt p₁ i isRec) :: env.consts⟩).find? cvTa.name).isSome
      = true
    exact consBlockInds_find?_isSome rest (i + 1) j _ cvTa h

/-- **The two former passes' η side conditions**, off the
constructors' freshness at the environment holding all `k` formers: a
member's η constructor is one of ITS OWN constructors, which is fresh
there — so it is no former's name, and it was fresh before the block
too. -/
theorem blockEtaSide_of {env envI : Env} {q : BlockShape} {F : Nat} {isRec : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {sortsss : List (List (List Level))}
    (hcons : envI = ConLeche.consBlockInds q isRec cvTas 0 env)
    (hlenCv : cvTas.length = q.k)
    (hnameOf : ∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
      cvTb.name = q.memberNames.getD j .anonymous)
    (hCtors : ConLeche.checkBlockCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI envI q
      (q.members.zip cvTas) = .ok (ctorsAs, sortsss))
    (hClps : ∀ c ∈ q.allCtors, c.1.levelParams = q.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false) :
    (∀ (j j' : Nat) (cvTa cvTb : ConstantVal), cvTas[j]? = some cvTa →
        cvTas[j']? = some cvTb → (ConLeche.blockCapsAt q j isRec).eta = true →
        cvTb.name ≠ (ConLeche.blockCapsAt q j isRec).etaCtor) ∧
    (∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
        (ConLeche.blockCapsAt q j isRec).eta = true →
        env.find? (ConLeche.blockCapsAt q j isRec).etaCtor = none) := by
  -- at an η-capable member the record names that member's ONE
  -- constructor, which the run stored and found fresh
  have hkey : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      (ConLeche.blockCapsAt q j isRec).eta = true →
      envI.find? (ConLeche.blockCapsAt q j isRec).etaCtor = none := by
    intro j cvTa hj he
    have hjk : j < q.k := by
      have := (List.getElem?_eq_some_iff.mp hj).1; rwa [hlenCv] at this
    obtain ⟨c, hc, hcaps⟩ | hcaps := blockCapsAt_cases q j isRec
    · have hrun := blockCtorRuns_of hCtors hnameOf j cvTa hjk hj
      obtain ⟨⟨hlenA, -⟩, hfacts⟩ := blockCtorFacts_of hrun (fun c' hc' => hClps c' (by
        rw [BlockShape.allCtors, List.mem_flatten]
        exact ⟨_, List.mem_map.mpr ⟨_, by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < q.members.length from hjk)]
          exact ⟨List.getElem_mem _, rfl⟩⟩, hc'⟩))
      rw [hc] at hlenA
      obtain ⟨cA, hcA⟩ : ∃ cA, (ctorsAs.getD j [])[0]? = some cA :=
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
      rw [hcons]; exact consBlockInds_find?_isSome _ _ _ _ _ hj'
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
theorem lfpCover_formers (mp : EnvModelM V μ env) {envI : Env} {q : BlockShape} {isRec : Bool}
    {cvTas : List ConstantVal}
    (hcons : envI = ConLeche.consBlockInds q isRec cvTas 0 env)
    (mpX : EnvModelM V μ envI)
    (hfresh : ∀ cvTb ∈ cvTas, env.find? cvTb.name = none)
    (hagX : ∀ n : Name, (∀ cvTb ∈ cvTas, n ≠ cvTb.name) → mpX.base2.acval n = mp.base2.acval n)
    {names : List Name} (hnames : ∀ cvTb ∈ cvTas, cvTb.name ∈ names)
    (hex : ∀ n ∈ names, env.find? n = none) :
    LfpCover mp [] → ∃ mk : EnvModelM V μ envI, mk.base2 = mpX.base2 ∧
      mk.lfpBlocks = mp.lfpBlocks ∧ LfpCover mk names := by
  intro h0
  obtain ⟨newI, hnewI, hnewIall⟩ := consBlockInds_consts (p₁ := q) (isRec := isRec) cvTas 0 env
  have henv : envI.consts = newI ++ env.consts := by rw [hcons]; exact hnewI
  obtain ⟨mk, hbk, hlk, hcov⟩ := lfpCover_append (ex := []) (ex' := names) mp mpX (new := newI) henv
    (fun n ci hf => by
      have hfr : ∀ c ∈ newI, env.find? c.name = none := by
        intro c hc
        obtain ⟨cv, hcv, j, rfl⟩ := hnewIall c hc
        exact hfresh cv hcv
      show List.find? _ _ = _
      rw [henv]
      exact find?_append_of_fresh hfr hf)
    (fun c hc tbl h => by
      obtain ⟨cv, -, j, rfl⟩ := hnewIall c hc
      exact nomatch h)
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
theorem blockTablesStage_of (hμ : μ.verifiedChecks = true) {F : Nat} {env envI : Env}
    {p₀ : BlockParts} {isRec : Bool} {cvTas : List ConstantVal} {q : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    {isorts : List (List Level)}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hlps₀ : ∀ ms ∈ p₀.members, ms.cvT.levelParams = p₀.lps)
    (hndM : q.memberNames.Nodup)
    (hndC : (q.allCtors.map (·.1.name)).Nodup)
    (hClps : ∀ c ∈ q.allCtors, c.1.levelParams = q.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false)
    (hInd : ConLeche.checkBlockInds (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p₀ isRec
      = .ok (envI, cvTas, q))
    (hCtors : ConLeche.checkBlockCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI envI q
      (q.members.zip cvTas) = .ok (ctorsAs, sortsss))
    (hsorts : ConLeche.checkBlockIdxSorts (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI q
      (q.members.zip cvTas) = .ok isorts)
    -- the positivity stage (`DeclBlockRun` 3): U2 grades the fields with holes
    {pP : BlockParts}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × ConLeche.NestState}
    (hPos : ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI
      envI.find? envI.consts pP cvTas ctorsAs = .ok posKs)
    (hpN : pP.memberNames = q.memberNames) (hpL : pP.lps = q.lps) (hpP : pP.nP = q.nP)
    (hpI : pP.nIdxs = q.nIdxs) (hpR : pP.resSort = q.resSort)
    (hfamFree : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < q.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (q.members.getD m default).nIdx = 0 → 0 < cA.2 →
      envI.find? (projFnName (q.memberNames.getD m .anonymous) 0) = none)
    (hprojTbl : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < q.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (q.members.getD m default).nIdx = 0 →
      envI.find? (projTableName (q.memberNames.getD m .anonymous)) = none)
    -- the input's coverage (the walk's container case reads the containers' clauses)
    (hcovIn : LfpCover mp []) :
    ∃ (pk : Nat → BlockMemberPick) (uOf : Nat → (Name → Nat) → Nat)
      (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (mpI : EnvModelM V μ envI),
      BlockNamesOk (V := V) (blockDataOf V q ctorsAs pk uOf ppsOf) cvTas ∧
      BlockTablesStage (V := V) μ F (blockDataOf V q ctorsAs pk uOf ppsOf) q.lps cvTas
        q isRec (blockLeafH (blockDataOf V q ctorsAs pk uOf ppsOf)) envI
        q.ctorNamesAt (fun m => (sortsss.getD m []).getD 0 []) ∧
      BlockCtorsCore mpI.base2 (blockDataOf V q ctorsAs pk uOf ppsOf) q.lps cvTas
        q isRec (blockLeafH (blockDataOf V q ctorsAs pk uOf ppsOf)) 0 ∧
      ConLeche.BlockEtaInv envI q.memberNames q.ctorNamesAt ∧
      (∀ (c j : Nat) (cA : ConstantVal × Nat),
        ((blockDataOf V q ctorsAs pk uOf ppsOf).ctorsM c)[j]? = some cA →
        envI.find? cA.1.name = none) ∧
      (∀ (c j : Nat) (cA : ConstantVal × Nat),
        ((blockDataOf V q ctorsAs pk uOf ppsOf).ctorsM c)[j]? = some cA →
        (blockDataOf V q ctorsAs pk uOf ppsOf).nfFF c j = (posKs.2.1.getD c []).getD j default) ∧
      -- every name off the block keeps its leaf
      ∀ n : Name, (∀ cvTb ∈ cvTas, n ≠ cvTb.name) → mpI.base2.acval n = mp.base2.acval n := by
  classical
  -- the run's shape: the k formers consed at once
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, hmem0, -, hq, hcons, -, -, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  have hqm : q.members = p₀.members := by rw [hq]; rfl
  have hne : 0 < q.members.length := by rw [hqm, hmem0]; simp
  have hlenN : q.memberNames.length = q.members.length := by
    show (q.members.map _).length = _; simp
  have hlenNI : q.nIdxs.length = q.memberNames.length := by
    show (q.members.map _).length = _; rw [hlenN]; simp
  -- the formers' data
  obtain ⟨ppsOf, sOf, hF⟩ := blockFormerFacts_of hμ mp hInd hlps₀
  -- the η side conditions of the two passes
  obtain ⟨hetaNe, hetaFresh⟩ :=
    blockEtaSide_of hcons hF.lenCv hF.nameOf hCtors hClps
  -- the constructors' lists, positionally
  obtain ⟨hlenCA, -, -⟩ := ConLeche.checkBlockCtors_inv hCtors
  have hlenCtorsAs : ctorsAs.length = q.k := by
    rw [hlenCA, List.length_zip, hF.lenCv]
    exact Nat.min_self _
  have hCA : ∀ m, m < q.k → ctorsAs[m]? = some (ctorsAs.getD m []) := by
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
  have hfacts : ∀ (m : Nat) (cvTa : ConstantVal), m < q.k → cvTas[m]? = some cvTa →
      ((ctorsAs.getD m []).length = (q.members.getD m default).ctors.length ∧
        (sortsss.getD m []).length = (q.members.getD m default).ctors.length) ∧
      ∀ (j : Nat) (cA : ConstantVal × Nat), (ctorsAs.getD m [])[j]? = some cA →
        ∃ (c : ConstantVal × Nat) (sorts : List Level),
          (q.members.getD m default).ctors[j]? = some c ∧
          cA.1.name = c.1.name ∧ cA.2 = c.2 ∧ cA.1.levelParams = q.lps ∧
          envI.find? cA.1.name = none ∧ cA.1.type.constsResolve envI = true ∧
          cA.1.name.isProjFnShape = false ∧
          ConLeche.reservedBasisNames.contains cA.1.name = false ∧
          (sortsss.getD m [])[j]? = some sorts ∧
          (cA.1.type.stripPis (q.nP + cA.2)).isSome = true ∧
          (∃ ty₀ : Expr, ty₀.hasFvar = false ∧
            ConLeche.annotateCore μ envI F 0 ty₀ = .ok cA.1.type) ∧
          ConLeche.checkSumCtor (ConLeche.fueledOps μ F) envI envI cvTa.name q.lps q.nP
            (q.nIdxs.getD m 0) q.resSort q.isProp q.large c.1 cA.2 cvTa = .ok (cA.1, sorts) :=
    fun m cvTa hm hcv =>
      blockCtorFacts_of (blockCtorRuns_of hCtors hF.nameOf m cvTa hm hcv)
        (fun c hc => hClps c (hmemCtors m hm c hc))
  -- ## the DUMMY pass: the k formers at the EMPTY chain lists
  obtain ⟨mpD, hEclD, hFDD, hfindD, hagD⟩ := blockDummyPass mp hInd hF hndM hE hetaNe hetaFresh
  -- coverage at the dummy carrier, the members exempt (the walk's container case)
  have hmemFresh : ∀ cvTb ∈ cvTas, env.find? cvTb.name = none := by
    intro cvTb hcvTb
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
    exact hF.freshOf t cvTb ht
  have hmemNames : ∀ cvTb ∈ cvTas, cvTb.name ∈ pP.memberNames := by
    intro cvTb hcvTb
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
    have htk : t < q.members.length := by
      have := (List.getElem?_eq_some_iff.mp ht).1; rw [hF.lenCv] at this; exact this
    rw [hF.nameOf t cvTb ht, hpN]
    exact getD_mem _ (by rw [hlenN]; exact htk)
  have hnamesFresh : ∀ n ∈ pP.memberNames, env.find? n = none := by
    intro n hn
    rw [hpN] at hn
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hn
    have htk : t < q.k := by
      have := (List.getElem?_eq_some_iff.mp ht).1; rw [hlenN] at this; exact this
    obtain ⟨cvTb, hcv⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact htk)⟩
    have hname := hF.nameOf t cvTb hcv
    rw [List.getD_eq_getElem?_getD, ht] at hname
    rw [← show cvTb.name = n from hname]
    exact hF.freshOf t cvTb hcv
  have hcovD : ∃ mk : EnvModelM V μ envI, mk.base2 = mpD.base2 ∧
      LfpCover mk pP.memberNames :=
    (lfpCover_formers mp hcons mpD hmemFresh hagD hmemNames hnamesFresh hcovIn).imp
      fun _ h => ⟨h.1, h.2.2⟩
  -- ## the members' index telescopes, at the dummy carrier
  obtain ⟨uOf, hIdxOf, hUparams⟩ :=
    blockIdxFacts_of (isRec := isRec) hμ mpD hsorts hF.lenCv
      (fun j cvTb hj => (hfindD j cvTb hj).1) hFDD hF.lpsOf
  -- ## the members' constructors, read at the dummy carrier
  have hpickOf : ∀ mp' : EnvModelM V μ envI,
      (∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
        envI.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt q j isRec))) →
      ∀ m : Nat, ∃ pk : BlockMemberPick, m < q.k →
      ∀ (j : Nat) (cA : ConstantVal × Nat), (ctorsAs.getD m [])[j]? = some cA →
        BlockCtorDataI mp'.base2 (q.memberNames.getD m .anonymous)
          q.lps cA.1 q.nP cA.2 (q.nIdxs.getD m 0) q.resSort q.isProp q.large
          (pk.idxF j) (pk.dsF j) (pk.esF j) (pk.srcsF j)
          (pk.fvsPF j) (pk.xFvsF j) (pk.xrestF j) := by
    intro mp' hfind m
    by_cases hm : m < q.k
    · obtain ⟨cvTa, hcv⟩ : ∃ cvTa, cvTas[m]? = some cvTa :=
        ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact hm)⟩
      obtain ⟨pk, hpk⟩ := blockCtorFunsAt hμ mp' hcv hF.nameOf hF.lpsOf hF.sEval
        hF.stripOf hfind
        (fun j cA hj => by
          obtain ⟨c, sorts, -, -, -, -, -, -, -, -, -, -, -, hCtor⟩ :=
            (hfacts m cvTa hm hcv).2 j cA hj
          exact ⟨c, sorts, hCtor⟩)
      exact ⟨pk, fun _ => hpk⟩
    · exact ⟨⟨fun _ => [], fun _ _ => [], fun _ _ => [], fun _ => [], fun _ => [], fun _ => [],
        fun _ => .bvar 0, fun _ _ => [], fun _ => .bvar 0⟩, fun hh => absurd hh hm⟩
  obtain ⟨pk₀, hpk₀, hnf₀, habs₀⟩ : ∃ pk₀ : Nat → BlockMemberPick, (∀ m : Nat, m < q.k →
      ∀ (j : Nat) (cA : ConstantVal × Nat), (ctorsAs.getD m [])[j]? = some cA →
        BlockCtorDataI mpD.base2 (q.memberNames.getD m .anonymous)
          q.lps cA.1 q.nP cA.2 (q.nIdxs.getD m 0) q.resSort q.isProp q.large
          ((pk₀ m).idxF j) ((pk₀ m).dsF j) ((pk₀ m).esF j) ((pk₀ m).srcsF j)
          ((pk₀ m).fvsPF j) ((pk₀ m).xFvsF j) ((pk₀ m).xrestF j)) ∧
      -- the positivity walk's normal forms (the run's output)
      (∀ (m j : Nat), (pk₀ m).nf j = if j < (ctorsAs.getD m []).length
        then (posKs.2.1.getD m []).getD j default else .bvar 0) ∧
      -- the fields with holes: the normal form's reading at the dummy carrier
      ∀ (m j : Nat) (ψ : Name → Nat), (pk₀ m).absF j ψ
        = nfFieldsRead mpD.base2.acval envI (q.nP + q.k) ((ctorsAs.getD m []).getD j default).2
            ((pk₀ m).nf j) ψ :=
    ⟨fun m => { (hpickOf mpD (fun j cvTb hj => (hfindD j cvTb hj).1) m).choose with
        nf := fun j => if j < (ctorsAs.getD m []).length
          then (posKs.2.1.getD m []).getD j default else .bvar 0
        absF := fun j ψ => nfFieldsRead mpD.base2.acval envI (q.nP + q.k)
          ((ctorsAs.getD m []).getD j default).2 (if j < (ctorsAs.getD m []).length
            then (posKs.2.1.getD m []).getD j default else .bvar 0) ψ },
      fun m => (hpickOf mpD (fun j cvTb hj => (hfindD j cvTb hj).1) m).choose_spec,
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  -- ## the readings every member's data is taken against
  have hProp : q.isProp = (Level.isEquiv q.resSort .zero == some true) := by rw [hq]; rfl
  have hProp' : q.isProp = true → (Level.isEquiv q.resSort .zero == some true) = true :=
    fun h => by rw [← hProp]; exact h
  have hcvOf : ∀ t : Nat, t < q.k → ∃ cvTb, cvTas[t]? = some cvTb :=
    fun t ht => ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact ht)⟩
  have hlenPpsOf : ∀ (t : Nat), t < q.k → ∀ ψ : Name → Nat,
      (ppsOf t ψ).length = q.nP + q.nIdxs.getD t 0 := by
    intro t ht ψ
    obtain ⟨cvTb, hcv⟩ := hcvOf t ht
    exact (hF.fdOf t cvTb hcv).len ψ
  have hρpOf : ∀ (ψ : Name → Nat) (ρp : Nat → V) (m : Nat), m < q.k →
      Sat V (((ppsOf m ψ).take q.nP).map (·.2.2)).reverse ρp →
      ∀ c, c < q.k → Sat V (((ppsOf c ψ).take q.nP).map (·.2.2)).reverse ρp :=
    fun ψ ρp m hm hρ c hc => (hF.paramsIff m c hm hc ψ ρp).mp hρ
  have hleafOfD : ∀ (t : Nat), t < q.k → ∀ ψ : Name → Nat, ∃ B,
      mpD.base2.acval (q.memberNames.getD t .anonymous) ψ
        = mkLamsC (q.resSort.eval ψ + 1) (ppsOf t ψ) B := by
    intro t ht ψ
    obtain ⟨cvTb, hcv⟩ := hcvOf t ht
    rw [← hF.nameOf t cvTb hcv, (hfindD t cvTb hcv).2 ψ]
    exact ⟨_, rfl⟩
  -- ## the DUMMY record: the field lists the members' leaves are built over
  let dZ : BlockData V := blockDataOf V q ctorsAs pk₀ uOf ppsOf
  have hlenFssZ : ∀ (m : Nat) (ψ : Name → Nat),
      (dZ.Fss m ψ).length = (ctorsAs.getD m []).length := by
    intro m ψ
    show (fssOfR _ _).length = _
    rw [fssOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hlenEssZ : ∀ (m : Nat) (ψ : Name → Nat),
      (dZ.Ess m ψ).length = (ctorsAs.getD m []).length := by
    intro m ψ
    show (essOfR _).length = _
    rw [essOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hFssZD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (ctorsAs.getD m [])[j]? = some cA →
      (dZ.Fss m ψ).getD j [] = (((pk₀ m).dsF j ψ).drop q.nP).map (·.2.2) :=
    fun _ _ _ _ hj => fssOfR_fixCtorDataList_getD hj
  have hEssZD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (ctorsAs.getD m [])[j]? = some cA → (dZ.Ess m ψ).getD j [] = (pk₀ m).esF j ψ :=
    fun _ _ _ _ hj => essOfR_fixCtorDataList_getD hj
  have hlenFsZ : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      m < q.k → (ctorsAs.getD m [])[j]? = some cA →
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
      ((((ppsOf c ψ).drop q.nP).map (·.2.2))).length = q.nIdxs.getD c 0 := by
    intro c ψ
    by_cases hc : c < q.k
    · simp [hlenPpsOf c hc ψ]
    · rw [hppsNil c hc ψ, hnIdxsNil c hc]; simp
  have hIdsBelow : ∀ (c : Nat) (ψ : Name → Nat),
      FieldsBelow q.nP (((ppsOf c ψ).drop q.nP).map (·.2.2)) := by
    intro c ψ
    by_cases hc : c < q.k
    · obtain ⟨cvTb, hcv⟩ := hcvOf c hc
      have h := (DomsBelow.drop q.nP ((hF.fdOf c cvTb hcv).below ψ)).fields
      rwa [Nat.zero_add] at h
    · rw [hppsNil c hc ψ]
      simp only [List.drop_nil, List.map_nil]
      trivial
  have hcdsParams : ∀ (c : Nat) (ψ₁ ψ₂ : Name → Nat), (∀ n ∈ q.lps, ψ₁ n = ψ₂ n) →
      dZ.cds c ψ₁ = dZ.cds c ψ₂ := by
    intro c ψ₁ ψ₂ hφ
    by_cases hc : c < q.k
    · obtain ⟨cvTa, hcv⟩ := hcvOf c hc
      refine fixCtorDataList_congr (ctorsAs.getD c []) 0 fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ : ∃ cAi, (ctorsAs.getD c [])[i]? = some cAi :=
        ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨-, -, -, -, -, hlpsi, -⟩ := (hfacts c cvTa hc hcv).2 i cAi hi'
      have hφ' : ∀ n ∈ cAi.1.levelParams, ψ₁ n = ψ₂ n := fun n hn => hφ n (by rwa [← hlpsi])
      have hD := hpk₀ c hc i cAi hi'
      obtain ⟨h1, h2⟩ := hD.params ψ₁ ψ₂ hφ'
      exact ⟨h1, h2, rfl, rfl⟩
    · have hnil : ctorsAs.getD c [] = [] := getD_of_le [] (by rw [hlenCtorsAs]; omega)
      show fixCtorDataList _ _ _ _ _ _ (ctorsAs.getD c []) 0
        = fixCtorDataList _ _ _ _ _ _ (ctorsAs.getD c []) 0
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
  have hnilCtors : ∀ c : Nat, ¬ c < q.k → ctorsAs.getD c [] = [] :=
    fun c hc => getD_of_le [] (by rw [hlenCtorsAs]; omega)
  have hctorLt : ∀ (c j : Nat) (cA : ConstantVal × Nat),
      (ctorsAs.getD c [])[j]? = some cA → c < q.k := by
    intro c j cA hj
    by_cases hc : c < q.k
    · exact hc
    · rw [hnilCtors c hc] at hj; exact nomatch hj
  have hNZ : BlockNamesOk (V := V) dZ cvTas :=
    ⟨fun c cvTb hc => (hF.nameOf c cvTb hc).symm,
      fun c j cA hj => by rw [hF.lenCv]; exact hctorLt c j cA hj, hF.lenCv⟩
  have hclosedZ : ∀ (c j : Nat) (cA : ConstantVal × Nat), (dZ.ctorsM c)[j]? = some cA →
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true := by
    intro c j cA hj
    have hck := hctorLt c j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf c hck
    obtain ⟨c', sorts, -, -, -, -, -, -, -, -, -, -, -, hCtor⟩ := (hfacts c cvTa hck hcv).2 j cA hj
    obtain ⟨hf, -, -, hb⟩ := ConLeche.direct_sum_ctor_typeWF hCtor
    exact ⟨hf, hb⟩
  have hlenP0 : ∀ (ψ : Name → Nat) (mm : Nat), mm < q.k →
      (((ppsOf mm ψ).take q.nP).map (·.2.2)).length = q.nP := by
    intro ψ mm hmm
    rw [List.length_map, List.length_take, hlenPpsOf mm hmm ψ]
    omega
  -- the members' formers, as the stored field shape facts' producer reads them
  have hformersI : ∀ (ψ : Name → Nat) (t : Nat), t < q.k → ∃ cv caps bs s,
      envI.find? (q.memberNames.getD t .anonymous) = some (.indInfo cv caps) ∧
      cv.levelParams = q.lps ∧
      cv.type.stripPis (q.nP + q.nIdxs.getD t 0) = some (bs, .sort s) ∧
      s.eval ψ = q.resSort.eval ψ := by
    intro ψ t ht
    obtain ⟨cvTb, hcv⟩ := hcvOf t ht
    obtain ⟨bs, hbs⟩ := hF.stripOf t cvTb hcv
    refine ⟨cvTb, ConLeche.blockCapsAt q t isRec, bs, sOf t, ?_, hF.lpsOf t cvTb hcv, hbs,
      hF.sEval t ψ⟩
    rw [← hF.nameOf t cvTb hcv]
    exact (hfindD t cvTb hcv).1
  have hTasI : ∀ cvT ∈ cvTas, cvT.type.hasFvar = false := by
    intro cvT hmem
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hmem
    exact (mpD.base2.wf _ (List.mem_of_find?_eq_some (hfindD t cvT ht).1)).1
  have hgetCA : ∀ (c j : Nat) (cA : ConstantVal × Nat), (ctorsAs.getD c [])[j]? = some cA →
      (ctorsAs.getD c []).getD j default = cA := fun c j cA hj => by
    rw [List.getD_eq_getElem?_getD, hj]; rfl
  -- the datum's normal forms are the run's, at every stored constructor
  have hnfZ : ∀ (c j : Nat) (cA : ConstantVal × Nat), (dZ.ctorsM c)[j]? = some cA →
      dZ.nfFF c j = (posKs.2.1.getD c []).getD j default := by
    intro c j cA hj
    show (pk₀ c).nf j = _
    rw [hnf₀, if_pos (show j < (ctorsAs.getD c []).length from (List.getElem?_eq_some_iff.mp hj).1)]
  have hFZ : ∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      envI.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt q c isRec)) ∧
      FormerData mpD.base2 cvTb (dZ.nP + dZ.nIdxAt c) dZ.resSort (dZ.ppsM c) :=
    fun c cvTb hc => ⟨(hfindD c cvTb hc).1, hFDD c cvTb hc⟩
  -- the fields with holes ARE the normal form's reading, at the dummy carrier
  have hAbsZ : ∀ (c j : Nat) (cA : ConstantVal × Nat), (dZ.ctorsM c)[j]? = some cA →
      BlockAbsRead mpD.base2 dZ q.lps c j cA := by
    intro c j cA hj
    have hck := hctorLt c j cA hj
    obtain ⟨hCf, hCb⟩ := hclosedZ c j cA hj
    refine blockAbsRead_of_run hμ mpD hNZ hFZ hPos hpN hpL hpP hpI hlenN.symm hndM
      (fun c hc => hCA c hc) hlenCtorsAs hclosedZ hformersI hck hj
      ((hpk₀ c hck j cA hj).storedCtorFacts hCf hCb) (hnfZ c j cA hj) (fun ψ => ?_)
    show (pk₀ c).absF j ψ = _
    rw [habs₀, hgetCA c j cA hj]
    rfl
  -- the normal forms' own facts: member-free, at the block's levels
  have hnfFacts : ∀ (c j : Nat) (cA : ConstantVal × Nat), (dZ.ctorsM c)[j]? = some cA →
      (dZ.nfFF c j).nestOcc q.memberNames 0 0 = false ∧ lpDefF q.lps (dZ.nfFF c j) = true := by
    intro c j cA hj
    have hck := hctorLt c j cA hj
    obtain ⟨hCf, hCb⟩ := hclosedZ c j cA hj
    obtain ⟨-, hocc, hlp, -⟩ := blockRunLink hμ mpD hNZ hFZ hPos hpN hpL hpP hpI hlenN.symm hndM
      (fun c hc => hCA c hc) hlenCtorsAs hclosedZ (fun _ => 0) (hformersI _) hck hj
      ((hpk₀ c hck j cA hj).storedCtorFacts hCf hCb)
    rw [hnfZ c j cA hj]
    exact ⟨hocc, hlp⟩
  have hctxZ : BlockHoleCtxFacts mpD.base2 dZ q.lps cvTas q isRec :=
    ⟨fun c cvTb hc => ⟨(hfindD c cvTb hc).1, hFDD c cvTb hc⟩,
      fun c j cA hj => ⟨hpk₀ c (hctorLt c j cA hj) j cA hj, hAbsZ c j cA hj⟩⟩
  have hHZ : BlockHoleFacts mpD.base2 dZ q.lps := by
    refine ⟨fun c _ j cA hj => hpk₀ c (hctorLt c j cA hj) j cA hj,
      fun ψ c hc j hj => (blockStoredShapes_of_run hμ mpD hNZ hctxZ hPos hpN hpL hpP hpI
        hlenN.symm hndM rfl (fun c hc => hCA c hc) hlenCtorsAs hclosedZ hnfZ ψ (hformersI ψ) hc
        hj),
      fun ψ => hlenP0 ψ 0 hk0, fun ψ mm hmm => hlenP0 ψ mm hmm,
      fun ψ mm hmm ρ h => (hF.paramsIff 0 mm hk0 hmm ψ ρ).mp h,
      fun ψ mm hmm ρ h => (hF.paramsIff 0 mm hk0 hmm ψ ρ).mpr h,
      fun ψ c _ j hj => ?_⟩
    obtain ⟨cA, hjA⟩ : ∃ cA, (ctorsAs.getD c [])[j]? = some cA :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    rw [hEssZD c j cA ψ hjA]
    show ((pk₀ c).esF j ψ).length = (((ppsOf c ψ).drop q.nP).map (·.2.2)).length
    rw [hIdsLen c ψ]
    exact (hpk₀ c (hctorLt c j cA hjA) j cA hjA).lenE ψ
  -- U2's grading, per constructor
  have hGZ := fun (ψ : Name → Nat) (c : Nat) (hc : c < dZ.N) (j : Nat)
      (hj : j < (dZ.ctorsM c).length) =>
    blockHoleGrade_of_run hμ mpD hNZ hctxZ hPos hpN hpL hpP hpI hpR hlenN.symm rfl
      (fun c hc => hCA c hc) hlenCtorsAs hclosedZ hnfZ ψ hc hj
  -- the hole chains: graded, bit-valid, closed
  have hchZ := fun (ψ : Name → Nat) => blockHoleChains_facts hHZ ψ
    (fun ρp hs c hc => by
      have hck : c < q.k := by have : c < q.k + 0 := hc; omega
      obtain ⟨cvTb, hcv⟩ := hcvOf c hck
      exact hIdxOf c cvTb hcv ψ ρp (hρpOf ψ ρp 0 hk0 hs c hck))
    (fun mm hmm => by
      obtain ⟨cvTb, hcv⟩ := hcvOf mm hmm
      exact teleTake_ok q.nP (fun ρ => (hFDD mm cvTb hcv).okTy ψ ρ) ((hFDD mm cvTb hcv).below ψ))
    (fun c _ => hIdsBelow c ψ) (fun c hc j hj => hGZ ψ c hc j hj)
  -- the hole chains depend on the block's level parameters only
  have hpp : ∀ (ψ₁ ψ₂ : Name → Nat), (∀ n ∈ q.lps, ψ₁ n = ψ₂ n) → ∀ c, ppsOf c ψ₁ = ppsOf c ψ₂ := by
    intro ψ₁ ψ₂ hφ c
    cases hc : cvTas[c]? with
    | none => rw [hF.ppsNil c hc, hF.ppsNil c hc]
    | some cvTb =>
      exact ((hF.fdOf c cvTb hc).params ψ₁ ψ₂
        (fun n hn => hφ n (by rw [← hF.lpsOf c cvTb hc]; exact hn))).1
  have hlpN : ∀ c j, lpDefF q.lps ((pk₀ c).nf j) = true := by
    intro c j
    by_cases hj : j < (ctorsAs.getD c []).length
    · exact (hnfFacts c j _ (List.getElem?_eq_getElem hj)).2
    · rw [hnf₀, if_neg hj]; rfl
  have hparamsH : ∀ ψ₁ ψ₂ : Name → Nat, (∀ n ∈ q.lps, ψ₁ n = ψ₂ n) →
      dZ.toLfp.holeChains ψ₁ = dZ.toLfp.holeChains ψ₂ := by
    intro ψ₁ ψ₂ hφ
    obtain ⟨hu, hfz, hes⟩ := hZparams ψ₁ ψ₂ hφ
    refine LfpDatum.holeChains_congr rfl (fun m => hu m)
      (fun m => by
        show ((ppsOf m ψ₁).take q.nP).map (·.2.2) = ((ppsOf m ψ₂).take q.nP).map (·.2.2)
        rw [hpp ψ₁ ψ₂ hφ m])
      (fun c => by
        show ((ppsOf c ψ₁).drop q.nP).map (·.2.2) = ((ppsOf c ψ₂).drop q.nP).map (·.2.2)
        rw [hpp ψ₁ ψ₂ hφ c])
      (fun _ => rfl) (fun c j => ?_) (fun c j => ?_)
    · show (pk₀ c).absF j ψ₁ = (pk₀ c).absF j ψ₂
      rw [habs₀, habs₀]
      exact nfFieldsRead_params mpD.base2 (hlpN c j) hφ
    · exact BlockData.absE_congr rfl (by rw [hes c]) (by rw [congrFun hfz c])
  -- ## the hole operator's fixed-point premises: monotone by
  -- positivity, closed by accessibility
  have hposZ := blockCtorPos_of_run hμ mpD hNZ hctxZ hPos hpN hpL hpP hpI hlenN.symm
    rfl hlenCtorsAs (fun c hc => hCA c hc) hclosedZ hnfZ hcovD
  have hfunZ : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (dZ.params ψ).reverse ρp →
      MonoTuple (dZ.w ψ) dZ.k (blockIdx (fun c => dZ.uM c ψ) ρp (fun c => dZ.IdsM c ψ))
        (blockPhiG dZ.k (dZ.w ψ) ρp (fun c => dZ.uM c ψ) (fun c => dZ.IdsM c ψ)
          (dZ.toLfp.holeChains ψ)) ∧
      ∃ L, IsClosedTuple (dZ.w ψ) dZ.k (blockIdx (fun c => dZ.uM c ψ) ρp (fun c => dZ.IdsM c ψ))
        (blockPhiG dZ.k (dZ.w ψ) ρp (fun c => dZ.uM c ψ) (fun c => dZ.IdsM c ψ)
          (dZ.toLfp.holeChains ψ)) L := by
    intro ψ ρp hs
    have hIdxZ : ∀ c, c < dZ.N → IdxOk (dZ.uM c ψ) ρp (dZ.IdsM c ψ) := fun c hc => by
      have hck : c < q.k := by have : c < q.k + 0 := hc; omega
      exact (hIdxOf c (hcvOf c hck).choose (hcvOf c hck).choose_spec ψ ρp
        (hρpOf ψ ρp 0 hk0 hs c hck)).1
    have hkN : dZ.toLfp.k ≤ dZ.toLfp.N := Nat.le_add_right _ _
    have hok : dZ.toLfp.HoleTmOk ψ ρp := fun m hm =>
      ⟨⟨(hHZ.parsLen ψ m hm).trans (hHZ.lenP ψ).symm, hHZ.parsSat ψ m hm ρp hs⟩,
        fun _ => (hIdxZ m (Nat.lt_of_lt_of_le hm hkN)).2⟩
    have hfib : ∀ X, InTupleSpace (dZ.toLfp.w ψ) dZ.toLfp.N (dZ.toLfp.idx ψ ρp) X →
        ∀ c, c < dZ.toLfp.N → ∀ t, t ∈ˢ dZ.toLfp.idx ψ ρp c → ∀ x,
          x ∈ˢ app (dZ.toLfp.Φ ψ ρp X c) t ↔
            ∃ j fs, dZ.toLfp.HFits ψ ρp X t c j fs ∧ x = dZ.toLfp.inj ψ c j fs := by
      intro X _ c hc t ht x
      have happ : ∀ j, j < dZ.toLfp.nctors c → dZ.toLfp.HolesApplied ψ c j :=
        fun j hj => blockHolesApplied hHZ ψ hc hj
      have hres : ∀ j, j < dZ.toLfp.nctors c →
          (dZ.toLfp.resIdx ψ c j).length = (dZ.toLfp.ids c ψ).length := by
        intro j hj
        show (dZ.absE ψ c j).length = (dZ.IdsM c ψ).length
        simp only [BlockData.absE, List.length_map]
        exact hHZ.lenE ψ c hc j hj
      exact LfpDatum.holeOp_fibre hok hkN X happ hres ht x
    refine ⟨monoTuple_of_tupRel (D := dZ.toLfp) hfib (hposZ ψ ρp hs), ?_⟩
    by_cases hw : dZ.w ψ = 0
    · have hmaps := blockPhi_maps_of ((hchZ ψ).1 ρp hs)
      rw [hw] at hmaps ⊢
      exact closedTuple_zero hmaps
    · -- (W) from accessibility, at every block
      have hGw : ∀ c, c < dZ.N → ∀ j, j < (dZ.ctorsM c).length →
          ∀ X, InTupleSpace (dZ.toLfp.w ψ) dZ.toLfp.N (dZ.toLfp.idx ψ ρp) X →
          FieldsOkB (dZ.w ψ) (dZ.toLfp.frame ψ ρp X) (dZ.absF ψ c j) :=
        fun c hc j hj X hX => (((hGZ ψ c hc j hj).2 ρp hs X hX)).1
      obtain ⟨A, hA, hacc⟩ : ∃ A, A ∈ˢ (univ (dZ.toLfp.w ψ) : V) ∧
          AccTuple (dZ.toLfp.w ψ) dZ.toLfp.N (dZ.toLfp.idx ψ ρp) dZ.toLfp.N
            (dZ.toLfp.idx ψ ρp) (dZ.toLfp.holeOp ψ ρp) A := by
        exact blockAcc_of_run hμ mpD hNZ hctxZ hHZ hPos hpN hpL hpP hpI hpR hlenN.symm
          rfl hlenCtorsAs (fun c hc => hCA c hc) hclosedZ hnfZ hcovD ψ ρp hs hw hIdxZ hGw
      exact closed_of_acc hw hA (blockPhi_maps_of ((hchZ ψ).1 ρp hs)) hacc
  -- a unit-like member's hole leaf folds to the one tagged empty tuple
  have hfoldZH : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      (ConLeche.blockCapsAt q j isRec).unitlike = true →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
        SpineFit ρ ((ppsOf j ψ).map (·.2.2)) ts →
        ts.foldl SetTheory.app (interp V ρ
            (blockTyG q.k (q.resSort.eval ψ) (fun c => uOf c ψ)
              (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) (dZ.toLfp.holeChains ψ)
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
    have hlenA : (ctorsAs.getD j []).length = 1 := by
      rw [(hfacts j cvTa hjk hcv).1.1, hcs]; rfl
    obtain ⟨cA, hcA⟩ : ∃ cA, (ctorsAs.getD j [])[0]? = some cA :=
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
    have hIds0 : ((ppsOf j ψ).drop q.nP).map (·.2.2) = [] := by
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
        show (ppsOf c ψ).length = q.nP + (((ppsOf c ψ).drop q.nP).map (·.2.2)).length
        rw [hIdsLen c ψ]; exact hlenPpsOf c hc ψ)
      hjk hIds0
      (fun ρp hs => fun c hc => (hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
        (hρpOf ψ ρp 0 hk0 hs c hc)).1)
      (fun ρp hs => (hchZ ψ).1 ρp hs) (hfunZ ψ)
      (fun ρp _ j' hj' i hi => by
        rw [hFss0] at hi
        have : j' = 0 := by
          have : j' < (ctorsAs.getD j []).length := hj'
          omega
        subst this
        exact absurd hi (Nat.not_lt_zero _))
      hsp
    rw [hFss0, hEss0, rChains_single_nil] at h
    exact h
  -- ## the REAL pass: the k formers at the HOLE leaves
  obtain ⟨mpR, hEclR, hFDR, hfindR, hagR⟩ :=
    blockRealPass (uOf := uOf) (Chs := fun ψ => dZ.toLfp.holeChains ψ)
      mp hInd hF hndM hE hetaNe hetaFresh hIdsLen hIdsBelow
      (fun ψ c hc => (hchZ ψ).2.2 c hc)
      (fun ψ₁ ψ₂ hφ => ⟨(hZparams ψ₁ ψ₂ hφ).1, hparamsH ψ₁ ψ₂ hφ⟩)
      (fun j hj ψ ρp hρp =>
        ⟨fun c hc => (hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
            (hρpOf ψ ρp j hj hρp c hc)).1,
          fun c hc => (hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
            (hρpOf ψ ρp j hj hρp c hc)).2⟩)
      (fun j hj ψ ρp hρp => (hchZ ψ).1 ρp (hρpOf ψ ρp j hj hρp 0 hk0))
      (fun j hj ψ ρp hρp Y hY c hc t _ =>
        (hchZ ψ).2.1 ρp (hρpOf ψ ρp j hj hρp 0 hk0) Y hY c hc t)
      hfoldZH
  -- ## the constructors, read again at the REAL carrier
  obtain ⟨pk, hpk, habsR⟩ : ∃ pk : Nat → BlockMemberPick, (∀ m : Nat, m < q.k →
      ∀ (j : Nat) (cA : ConstantVal × Nat), (ctorsAs.getD m [])[j]? = some cA →
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
      (ctorsAs.getD m [])[j]? = some cA →
      ((blockDataOf V q ctorsAs pk uOf ppsOf).Ess m ψ).getD j [] = (pk m).esF j ψ :=
    fun _ _ _ _ hj => essOfR_fixCtorDataList_getD hj
  -- ## the fields with holes are the walked term's reading at the REAL
  -- carrier too: it agrees with the dummy one off the members, and the
  -- walked term looks up no member (M2′, `nfFieldsRead_agree`)
  have hmemName : ∀ t, t < q.k → q.memberNames.getD t .anonymous ∈ q.memberNames := fun t ht =>
    getD_mem _ (by rw [hlenN]; exact ht)
  have hagDR : ∀ n, n ∉ q.memberNames → mpD.base2.acval n = mpR.base2.acval n := by
    intro n hn
    have hne' : ∀ cvTb ∈ cvTas, n ≠ cvTb.name := by
      intro cvTb hcvTb hh
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
      have htk : t < q.k := by
        have := (List.getElem?_eq_some_iff.mp ht).1; rwa [hF.lenCv] at this
      exact hn (by rw [hh, hF.nameOf t cvTb ht]; exact hmemName t htk)
    rw [hagR n hne', hagD n hne']
  have hlitI := blockMembers_notLit mp.base2.wf (cvTas := cvTas) (names := q.memberNames)
    (envI := envI)
    (fun n => ⟨fun hn => by
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
        rw [← hh, hF.nameOf t cvTb ht]; exact hmemName t htk⟩)
    (fun cvTb hcvTb => by
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
      obtain ⟨bs, hbs⟩ := hF.stripOf t cvTb ht
      exact ⟨⟨_, (hfindD t cvTb ht).1⟩, _, bs, _, hbs⟩)
    (fun cvTb hcvTb => by
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
      exact hF.freshOf t cvTb ht)
    (fun n hn => by rw [hcons]; exact consBlockInds_find?_of_ne hn)
  have hoccI := canonOcc_of_positivity hPos (d := dZ) hpN hpL hlenN.symm (fun c hc => hCA c hc)
  have hAbsR : ∀ (c j : Nat) (cA : ConstantVal × Nat),
      ((blockDataOf V q ctorsAs pk uOf ppsOf).ctorsM c)[j]? = some cA →
      BlockAbsRead mpR.base2 (blockDataOf V q ctorsAs pk uOf ppsOf) q.lps c j cA := by
    intro c j cA hj
    have hck := hctorLt c j cA hj
    obtain ⟨hCf, hCb⟩ := hclosedZ c j cA hj
    refine blockAbsRead_of_run (d := blockDataOf V q ctorsAs pk uOf ppsOf) hμ mpR hNZ
      (fun c cvTb hc => ⟨(hfindR c cvTb hc).1, hFDR c cvTb hc⟩)
      hPos hpN hpL hpP hpI hlenN.symm hndM
      (fun c hc => hCA c hc) hlenCtorsAs hclosedZ hformersI hck hj
      ((hpk c hck j cA hj).storedCtorFacts hCf hCb)
      (by show (pk c).nf j = _; rw [(habsR c).2]; exact hnfZ c j cA hj) (fun ψ => ?_)
    show (pk c).absF j ψ = _
    rw [(habsR c).1, habs₀, hgetCA c j cA hj]
    show _ = nfFieldsRead _ _ _ _ ((pk c).nf j) ψ
    rw [(habsR c).2]
    exact nfFieldsRead_agree hagDR (hnfFacts c j cA hj).1 hlitI.1 hlitI.2 ψ
  -- the result index readings with holes agree too: the two carriers
  -- read the canonical crest alike
  have hAbsE : ∀ (c j : Nat) (cA : ConstantVal × Nat), (ctorsAs.getD c [])[j]? = some cA →
      ∀ ψ : Name → Nat, (blockDataOf V q ctorsAs pk uOf ppsOf).absE ψ c j = dZ.absE ψ c j := by
    intro c j cA hj ψ
    have hck := hctorLt c j cA hj
    obtain ⟨-, A, hA, hr⟩ := hAbsZ c j cA hj
    obtain ⟨-, A', hA', hr'⟩ := hAbsR c j cA hj
    obtain rfl : A = A' := Option.some.inj (hA.symm.trans hA')
    obtain ⟨ab, -, hab, -, hlab, -⟩ := hr ψ
    obtain ⟨ab', -, hab', -, hlab', -⟩ := hr' ψ
    have e1 : denoteMeta mpD.base2.acval envI ψ (q.nP + q.k) A
        = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (q.k - 1 - c)))
            (paramBvarsAt q.nP (q.nP + q.k + cA.2) ++ dZ.absE ψ c j))) := hab
    have e2 : denoteMeta mpR.base2.acval envI ψ (q.nP + q.k) A
        = some (mkPisAV ab' (AnnotTerm.mkAppN (.bvar (cA.2 + (q.k - 1 - c)))
            (paramBvarsAt q.nP (q.nP + q.k + cA.2)
              ++ (blockDataOf V q ctorsAs pk uOf ppsOf).absE ψ c j))) := hab'
    rw [← canonCrest_read_agree hagDR (hoccI c hck j cA hj) hlitI.1 hlitI.2 hA ψ, e1] at e2
    obtain ⟨-, hX⟩ := mkPisAV_inj (hlab.trans hlab'.symm) (Option.some.inj e2)
    have hl : (paramBvarsAt q.nP (q.nP + q.k + cA.2) ++ dZ.absE ψ c j).length
        = (paramBvarsAt q.nP (q.nP + q.k + cA.2)
            ++ (blockDataOf V q ctorsAs pk uOf ppsOf).absE ψ c j).length := by
      simp only [List.length_append, BlockData.absE, List.length_map]
      rw [hEssZD c j cA ψ hj, hEssRD c j cA ψ hj, (hpk₀ c hck j cA hj).lenE ψ,
        (hpk c hck j cA hj).lenE ψ]
    exact (List.append_cancel_left (AnnotTerm.mkAppN_inj hX hl).2).symm
  have hresIm : ∀ e : Expr, e.constsResolve env = true → e.constsResolve envI = true := by
    intro e he
    rw [hcons]
    exact consBlockInds_constsResolve _ _ _ e he
  -- ## the REAL record's own readings, and the chain facts at them
  have hleafOfR : ∀ (t : Nat), t < q.k → ∀ ψ : Name → Nat, ∃ B,
      mpR.base2.acval (q.memberNames.getD t .anonymous) ψ
        = mkLamsC (q.resSort.eval ψ + 1) (ppsOf t ψ) B := by
    intro t ht ψ
    obtain ⟨cvTb, hcv⟩ := hcvOf t ht
    rw [← hF.nameOf t cvTb hcv, (hfindR t cvTb hcv).2 ψ]
    exact ⟨_, rfl⟩
  have hFssRD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (ctorsAs.getD m [])[j]? = some cA →
      ((blockDataOf V q ctorsAs pk uOf ppsOf).Fss m ψ).getD j []
        = (((pk m).dsF j ψ).drop q.nP).map (·.2.2) :=
    fun _ _ _ _ hj => fssOfR_fixCtorDataList_getD hj
  -- ## the REAL record's fields with holes are the dummy one's:
  -- the two readings agree off the recursive fields
  have hholeEq : ∀ ψ : Name → Nat,
      (blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.holeChains ψ
        = dZ.toLfp.holeChains ψ := by
    intro ψ
    have hgetNil : ∀ (L : List (List AnnotTerm)) (j : Nat), L.length ≤ j → L.getD j [] = [] :=
      fun L j h => getD_of_le [] h
    have hlenEssR : ∀ m, ((blockDataOf V q ctorsAs pk uOf ppsOf).Ess m ψ).length
        = (ctorsAs.getD m []).length := by
      intro m
      show (essOfR _).length = _
      rw [essOfR_length]
      exact fixCtorDataList_length _ _ _ _ _ _ _ _
    have hlenFssR : ∀ m, ((blockDataOf V q ctorsAs pk uOf ppsOf).Fss m ψ).length
        = (ctorsAs.getD m []).length := by
      intro m
      show (fssOfR _ _).length = _
      rw [fssOfR_length]
      exact fixCtorDataList_length _ _ _ _ _ _ _ _
    refine LfpDatum.holeChains_congr rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun c j => ?_) (fun c j => ?_)
    · -- the fields with holes: the dummy datum's, shared
      show (pk c).absF j ψ = (pk₀ c).absF j ψ
      rw [(habsR c).1]
    · by_cases hj : j < (ctorsAs.getD c []).length
      · obtain ⟨cA, hjA⟩ : ∃ cA, (ctorsAs.getD c [])[j]? = some cA :=
          ⟨_, List.getElem?_eq_getElem hj⟩
        exact hAbsE c j cA hjA ψ
      · refine BlockData.absE_congr rfl ?_ ?_
        · rw [hgetNil _ _ (by rw [hlenEssR c]; omega), hgetNil _ _ (by rw [hlenEssZ c ψ]; omega)]
        · rw [hgetNil _ _ (by rw [hlenFssR c]; omega), hgetNil _ _ (by rw [hlenFssZ c ψ]; omega)]
  -- ## the constructors' frames at the real carrier
  have hframes : ∀ (m : Nat), m < q.k → ∀ (j : Nat) (cA : ConstantVal × Nat),
      (ctorsAs.getD m [])[j]? = some cA →
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsOf m ψ).take q.nP).map (·.2.2)).reverse ρ ↔
          Sat V ((((pk m).dsF j ψ).take q.nP).map (·.2.2)).reverse ρ) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V ((((pk m).dsF j ψ).take q.nP).map (·.2.2)).reverse ρ →
          FieldsOkB (q.resSort.eval ψ) ρ ((((pk m).dsF j ψ).drop q.nP).map (·.2.2)) ∧
          FieldsValid ρ ((((pk m).dsF j ψ).drop q.nP).map (·.2.2)) ∧
          (q.isProp = false →
            FieldsBound (q.resSort.eval ψ) ρ ((((pk m).dsF j ψ).drop q.nP).map (·.2.2))) ∧
          (∀ bs : List V, SpineFit ρ ((((pk m).dsF j ψ).drop q.nP).map (·.2.2)) bs →
            (∀ E ∈ (pk m).esF j ψ, WellDenotedV V (consList bs ρ) E) ∧
            SpineFit ρ (((ppsOf m ψ).drop q.nP).map (·.2.2))
              (idxValsAt ρ ((pk m).esF j ψ) bs))) := by
    intro m hm j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf m hm
    obtain ⟨c, sorts, -, -, -, -, -, -, -, -, -, -, -, hCtor⟩ := (hfacts m cvTa hm hcv).2 j cA hj
    have hTname : cvTa.name = q.memberNames.getD m .anonymous := hF.nameOf m cvTa hcv
    have hfT : envI.find? (q.memberNames.getD m .anonymous)
        = some (.indInfo cvTa (ConLeche.blockCapsAt q m isRec)) := by
      rw [← hTname]; exact (hfindR m cvTa hcv).1
    rw [hTname] at hCtor
    obtain ⟨h1, h2, -⟩ := ctorFramesGen hμ mpR hCtor hfT hProp' (hFDR m cvTa hcv)
      (hpk m hm j cA hj).toCtorDataI (hleafOfR m hm)
    exact ⟨h1, h2⟩
  -- ## the block's names, member by member
  have hnamesEq : ∀ (m : Nat), m < q.k →
      (ctorsAs.getD m []).map (·.1.name)
        = (q.members.getD m default).ctors.map (·.1.name) := by
    intro m hm
    obtain ⟨cvTa, hcv⟩ := hcvOf m hm
    refine List.ext_getElem? fun i => ?_
    rw [List.getElem?_map, List.getElem?_map]
    cases hi : (ctorsAs.getD m [])[i]? with
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
  -- ## the table stage's two freshness facts, at the capability record
  -- and at the guarded members (the run supplies them in the CHECKED
  -- lists' form; the capability reading is this proof's)
  have hsingle : ∀ (m : Nat) (cA : ConstantVal × Nat), m < q.k → ctorsAs.getD m [] = [cA] →
      ∃ sorts : List Level, sortsss.getD m [] = [sorts] := by
    intro m cA hm hcs
    obtain ⟨cvTa, hcv⟩ := hcvOf m hm
    obtain ⟨⟨hlenA, hlenS⟩, -⟩ := hfacts m cvTa hm hcv
    rw [hcs] at hlenA
    exact List.length_eq_one_iff.mp (by rw [hlenS, ← hlenA]; rfl)
  have hfamFree' : ∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      (ConLeche.blockCapsAt q c isRec).unitlike = false →
      (ConLeche.blockCapsAt q c isRec).eta = true →
      envI.find? (projFnName cvTb.name 0) = none := by
    intro c cvTb hcv hU hEta
    have hck : c < q.k := by
      have := (List.getElem?_eq_some_iff.mp hcv).1; rwa [hF.lenCv] at this
    obtain ⟨cc, hccs, hcaps⟩ | hcaps := blockCapsAt_cases q c isRec
    case inr => rw [hcaps] at hEta; exact nomatch hEta
    rw [hcaps] at hEta hU
    have hnIdx0 : (q.members.getD c default).nIdx = 0 := by
      have h := hEta
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.1.1
    obtain ⟨cvTa, hcvTa⟩ := hcvOf c hck
    have hlenA : (ctorsAs.getD c []).length = 1 := by
      rw [(hfacts c cvTa hck hcvTa).1.1, hccs]; rfl
    obtain ⟨cA, hcA⟩ := List.length_eq_one_iff.mp hlenA
    obtain ⟨sorts, hsorts'⟩ := hsingle c cA hck hcA
    have hnF : cA.2 = cc.2 := by
      obtain ⟨c', -, hc', -, hnF', -⟩ := (hfacts c cvTa hck hcvTa).2 0 cA (by rw [hcA]; rfl)
      rw [hccs] at hc'
      obtain rfl : cc = c' := by simpa using hc'
      exact hnF'
    have hpos : 0 < cA.2 := by
      rcases Nat.eq_zero_or_pos cA.2 with h0 | h0
      · exfalso
        rw [hnF] at h0
        rw [hnIdx0, h0] at hU
        simp at hU
        simp [hU] at hEta
      · exact h0
    rw [hF.nameOf c cvTb hcv]
    exact hfamFree c cA sorts hck hcA hsorts' hnIdx0 hpos
  have hprojTbl' : ∀ m, m < q.k → (∃ cAm, ctorsAs.getD m [] = [cAm]) → q.nIdxs.getD m 0 = 0 →
      envI.find? (projTableName (q.memberNames.getD m .anonymous)) = none := by
    rintro m hm ⟨cA, hcA⟩ hn0
    obtain ⟨sorts, hsorts'⟩ := hsingle m cA hm hcA
    refine hprojTbl m cA sorts hm hcA hsorts' ?_
    rw [← blockNIdxs_getD (q := q) (j := m) hm]
    exact hn0
  -- ## the constructors' stage invariant at the REAL carrier
  have hcoreR : BlockCtorsCore mpR.base2 (blockDataOf V q ctorsAs pk uOf ppsOf)
      q.lps cvTas q isRec (blockLeafH (blockDataOf V q ctorsAs pk uOf ppsOf)) 0 := by
    refine ⟨fun c cvTb hc => ⟨(hfindR c cvTb hc).1, hresIm _ (hF.resolveOf c cvTb hc),
        fun ψ => by rw [(hfindR c cvTb hc).2 ψ]; unfold blockLeafH; rw [hholeEq ψ]; rfl,
        hFDR c cvTb hc⟩,
      hfamFree', fun c j cA hj => ?_, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
    have hck : c < q.k := hctorLt c j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf c hck
    obtain ⟨-, -, -, -, -, -, -, hres, -⟩ := (hfacts c cvTa hck hcv).2 j cA hj
    have hD := hpk c hck j cA hj
    refine ⟨hres, fun e he => ?_, hD, hAbsR c j cA hj⟩
    exact hD.idxArgs_resolve hres e he
  -- ## the k formers' leaves: closed, and the members' values at the REAL carrier
  have hacvR : ∀ c, c < q.k → ∀ ψ : Name → Nat,
      mpR.base2.acval ((blockDataOf V q ctorsAs pk uOf ppsOf).memberName c) ψ
        = blockLeafH (blockDataOf V q ctorsAs pk uOf ppsOf) c ψ := by
    intro c hc ψ
    obtain ⟨cvTb, hcvTb⟩ := hcvOf c hc
    rw [show (blockDataOf V q ctorsAs pk uOf ppsOf).memberName c = cvTb.name from
      (hF.nameOf c cvTb hcvTb).symm]
    exact (hcoreR.1 c cvTb hcvTb).2.2.1 ψ
  -- ## the stored field shape facts at the REAL carrier
  have hShR : ∀ (ψ : Name → Nat) (c : Nat),
      c < (blockDataOf V q ctorsAs pk uOf ppsOf).N → ∀ j,
      j < ((blockDataOf V q ctorsAs pk uOf ppsOf).ctorsM c).length →
      StoredFieldShapes V q.k q.nP (q.resSort.eval ψ) (fun t => q.nIdxs.getD t 0)
        (fun t => mpR.base2.acval (q.memberNames.getD t .anonymous) ψ)
        ((blockDataOf V q ctorsAs pk uOf ppsOf).params ψ).reverse
        ((blockDataOf V q ctorsAs pk uOf ppsOf).absF ψ c j)
        (((blockDataOf V q ctorsAs pk uOf ppsOf).Fss c ψ).getD j []) :=
    fun ψ c hc j hj => (blockStoredShapes_of_run (d := blockDataOf V q ctorsAs pk uOf ppsOf)
      hμ mpR hNZ hcoreR.holeCtx hPos hpN hpL hpP hpI
      hlenN.symm hndM rfl (fun c hc => hCA c hc) hlenCtorsAs hclosedZ
      (fun c j cA hj => by show (pk c).nf j = _; rw [(habsR c).2]; exact hnfZ c j cA hj)
      ψ (hformersI ψ) hc hj)
  -- ## the constructors' stage, assembled
  have hSC : BlockCtorsStage (V := V) μ F (blockDataOf V q ctorsAs pk uOf ppsOf)
      q.lps cvTas q isRec (blockLeafH (blockDataOf V q ctorsAs pk uOf ppsOf))
      envI q.ctorNamesAt := by
    have hmnameEq : ∀ (m : Nat) (cvTa : ConstantVal), m < q.k → cvTas[m]? = some cvTa →
        (q.members.getD m default).cvT.name = cvTa.name := by
      intro m cvTa hm hcv
      have h1 : q.memberNames.getD m .anonymous = (q.members.getD m default).cvT.name := by
        rw [ConLeche.BlockShape.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hm, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hm]
        rfl
      rw [hF.nameOf m cvTa hcv, h1]
    have hmemIdx : ∀ (m : Nat) (cA : ConstantVal × Nat), cA ∈ ctorsAs.getD m [] →
        ∃ j, (ctorsAs.getD m [])[j]? = some cA := fun _ _ h => List.getElem?_of_mem h
    refine
      { leaf := fun _ _ => rfl
        holeOk := fun ψ ρp hs => by
          rw [hholeEq ψ]
          exact (hchZ ψ).1 ρp hs
        holeFun := fun ψ ρp hs => by
          rw [hholeEq ψ]
          exact hfunZ ψ ρp hs
        inst := rfl
        shapes := fun ψ c hc j hj =>
          (hShR ψ c (Nat.lt_of_lt_of_le hc (Nat.le_add_right _ _)) j hj).congr_leaf
            fun t ht => hacvR t ht ψ
        ctors := fun m cvTa hm hcv =>
          ⟨_, _, blockCtorRuns_of hCtors hF.nameOf m cvTa hm hcv⟩
        nodup := ?_
        out := ?_
        lpsT := fun m cvTa hm hcv => hF.lpsOf m cvTa hcv
        lpsA := ?_
        pshape := ?_
        ndBlock := ?_
        paramsOf := fun m hm ψ ρp hρ c hc => hρpOf ψ ρp m hm hρ c hc
        lenPps := ?_
        lenIds := fun m hm ψ => hIdsLen m ψ
        idxOk := ?_
        frames := ?_
        capsU := ?_ }
    · -- nodup
      intro m hm
      show ((ctorsAs.getD m []).map (·.1.name)).Nodup
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
    · -- pshape
      intro m hm cA hcA
      obtain ⟨j, hj⟩ := hmemIdx m cA hcA
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      obtain ⟨-, -, -, -, -, -, -, -, hps, -⟩ := (hfacts m cvTa hm hcv).2 j cA hj
      exact hps
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
      show (ppsOf c ψ).length = q.nP + (((ppsOf c ψ).drop q.nP).map (·.2.2)).length
      rw [hIdsLen c ψ]
      exact hlenPpsOf c hc ψ
    · -- idxOk
      intro m hm ψ ρp hρp c hc
      exact (hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
        (hρpOf ψ ρp m hm hρp c hc)).1
    · -- frames
      intro m hm j cA hj
      exact ⟨(hframes m hm j cA hj).1, fun ψ ρ hρ =>
        ⟨((hframes m hm j cA hj).2 ψ ρ hρ).1, ((hframes m hm j cA hj).2 ψ ρ hρ).2.1,
          fun bs hbs => (((hframes m hm j cA hj).2 ψ ρ hρ).2.2.2 bs hbs).2⟩⟩
    · -- capsU
      intro m hm cvTa hcv env' m' kk cA hkk hu hFD' hleaf' hleafC'
      have hnIdx0 : q.nIdxs.getD m 0 = 0 := by
        rw [blockNIdxs_getD (q := q) (j := m) hm]
        exact blockCapsAt_unitlike_nIdx hu
      obtain ⟨c, hcs, hcaps⟩ | hcaps := blockCapsAt_cases q m isRec
      case inr => rw [hcaps] at hu; exact nomatch hu
      have hlenA : (ctorsAs.getD m []).length = 1 := by
        rw [(hfacts m cvTa hm hcv).1.1, hcs]; rfl
      have hkk0 : kk = 0 := by
        have hlt : kk < (ctorsAs.getD m []).length := (List.getElem?_eq_some_iff.mp hkk).1
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
          (blockDataOf V q ctorsAs pk uOf ppsOf).Fss m ψ = [[]] := by
        intro ψ
        have hl1 : ((blockDataOf V q ctorsAs pk uOf ppsOf).Fss m ψ).length
            = (ctorsAs.getD m []).length := by
          show (fssOfR _ _).length = _
          rw [fssOfR_length]
          exact fixCtorDataList_length _ _ _ _ _ _ _ _
        obtain ⟨Fs, hFs⟩ := List.length_eq_one_iff.mp (hl1.trans hlenA)
        have h0 := hFssRD m 0 cA ψ hkk
        rw [hFs] at h0 ⊢
        simp only [List.getD_cons_zero] at h0
        rw [h0]
        have : (((pk m).dsF 0 ψ).drop q.nP).map (·.2.2) = [] := by
          refine List.length_eq_zero_iff.mp ?_
          simp [hlenD ψ]
        rw [this]
      refine blockCapsLawsAt m' (T := cvTa.name) (w := fun ψ => q.resSort.eval ψ)
        (pps := ppsOf m) (ds := (pk m).dsF 0) (L := fun ψ =>
          blockLeafH (blockDataOf V q ctorsAs pk uOf ppsOf) m ψ)
        (fun hU _ => absurd hu (by rw [hU]; simp))
        (fun ψ => (hlenP ψ).symm) hleaf' hFD'.read hFD'.okTy ?_ ?_ ?_
      · -- the fold at the fieldless shape
        intro _ ψ ρ ts hsp
        unfold blockLeafH
        rw [hholeEq ψ]
        exact hfoldZH m cvTa hcv hu ψ ρ ts hsp
      · -- the one constructor's leaf
        intro _ ψ
        have hleafCraw : m'.acval cA.1.name ψ
            = sumMkAV (q.resSort.eval ψ) 0 ((pk m).dsF 0 ψ)
                ((((pk m).dsF 0 ψ).drop q.nP).map (·.2.2))
                (uChains ((blockDataOf V q ctorsAs pk uOf ppsOf).Fss m ψ)) :=
          hleafC' ψ
        have hnil : (((pk m).dsF 0 ψ).drop q.nP).map (·.2.2) = [] := by
          refine List.length_eq_zero_iff.mp ?_
          simp [hlenD ψ]
        rw [hnil, hFss1 ψ] at hleafCraw
        rw [hcaps]
        show m'.acval c.1.name ψ = _
        rw [← hnameC]
        exact hleafCraw
      · -- the parameter spine fits the constructor's parameters
        intro ψ ρ as hsp
        refine (spineFit_iff_of_sat_iff (by rw [List.length_map, List.length_map,
          hlenP ψ, hlenD ψ]) (fun ρ' => ?_) ρ as (by rw [hsp.length_eq, List.length_map])).mp hsp
        have hiff := (hframes m hm 0 cA hkk).1 ψ ρ'
        rwa [List.take_of_length_le (Nat.le_of_eq (hlenP ψ)),
          List.take_of_length_le (Nat.le_of_eq (hlenD ψ))] at hiff
  have hmnameNe' : ∀ (c m : Nat), c < q.k → m < q.k → c ≠ m →
      q.memberNames.getD c .anonymous ≠ q.memberNames.getD m .anonymous := by
    intro c m hc hm hcm
    have hgc : q.memberNames.getD c .anonymous
        = q.memberNames[c]'(by rw [hlenN]; exact hc) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenN]; exact hc)]; rfl
    have hgm : q.memberNames.getD m .anonymous
        = q.memberNames[m]'(by rw [hlenN]; exact hm) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenN]; exact hm)]; rfl
    rw [hgc, hgm]
    exact nodup_getElem_ne hndM _ _ hcm
  -- ## the fields' sorts, as the constructors' run read them
  have hsortsAt : ∀ (m : Nat), m < q.k → ∀ (j : Nat) (cA : ConstantVal × Nat),
      (ctorsAs.getD m [])[j]? = some cA →
      ∃ sorts : List Level, (sortsss.getD m [])[j]? = some sorts ∧ sorts.length = cA.2 ∧
        (∀ i, i < cA.2 → q.isProp = false →
          Level.leq (sorts.getD i .zero) q.resSort = some true) ∧
        ∀ (ψ : Name → Nat) (ρ : Nat → V),
          Sat V ((((pk m).dsF j ψ).take q.nP).map (·.2.2)).reverse ρ →
          ∀ i, i < cA.2 → ∀ as : List V,
            SpineFit ρ (((((pk m).dsF j ψ).drop q.nP).map (·.2.2)).take i) as →
            interp V (consList as ρ)
                (((((pk m).dsF j ψ).drop q.nP).map (·.2.2)).getD i default)
              ∈ˢ (univ ((sorts.getD i .zero).eval ψ) : V) := by
    intro m hm j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf m hm
    obtain ⟨c, sorts, -, -, -, -, -, -, -, -, hsj, -, -, hCtor⟩ := (hfacts m cvTa hm hcv).2 j cA hj
    have hTname : cvTa.name = q.memberNames.getD m .anonymous := hF.nameOf m cvTa hcv
    have hfT : envI.find? (q.memberNames.getD m .anonymous)
        = some (.indInfo cvTa (ConLeche.blockCapsAt q m isRec)) := by
      rw [← hTname]; exact (hfindR m cvTa hcv).1
    rw [hTname] at hCtor
    obtain ⟨-, -, hlenS, hleq, hsorts3⟩ := ctorFramesGen hμ mpR hCtor hfT hProp' (hFDR m cvTa hcv)
      (hpk m hm j cA hj).toCtorDataI (hleafOfR m hm)
    exact ⟨sorts, hsj, hlenS, hleq, fun ψ ρ hρ i hi as hsp => hsorts3 ψ ρ hρ i hi as hsp⟩
  -- the constructors' hole facts at the REAL carrier
  have hHR : BlockHoleFacts mpR.base2 (blockDataOf V q ctorsAs pk uOf ppsOf) q.lps := by
    refine ⟨fun c _ j cA hj => hpk c (hctorLt c j cA hj) j cA hj,
      hShR,
      fun ψ => hlenP0 ψ 0 hk0, fun ψ mm hmm => hlenP0 ψ mm hmm,
      fun ψ mm hmm ρ h => (hF.paramsIff 0 mm hk0 hmm ψ ρ).mp h,
      fun ψ mm hmm ρ h => (hF.paramsIff 0 mm hk0 hmm ψ ρ).mpr h,
      fun ψ c _ j hj => ?_⟩
    obtain ⟨cA, hjA⟩ : ∃ cA, (ctorsAs.getD c [])[j]? = some cA :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    rw [hEssRD c j cA ψ hjA]
    show ((pk c).esF j ψ).length = (((ppsOf c ψ).drop q.nP).map (·.2.2)).length
    rw [hIdsLen c ψ]
    exact (hpk c (hctorLt c j cA hjA) j cA hjA).lenE ψ
  -- ## a structure-like member's leaf folds to its one constructor's fibre
  have hfoldT : ∀ (m : Nat) (cA : ConstantVal × Nat), m < q.k → ctorsAs.getD m [] = [cA] →
      q.nIdxs.getD m 0 = 0 →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
        SpineFit ρ ((ppsOf m ψ).map (·.2.2)) ts →
        ts.foldl SetTheory.app (interp V ρ
            (blockLeafH (blockDataOf V q ctorsAs pk uOf ppsOf) m ψ))
          = sumSet (q.resSort.eval ψ) (sumFibre (q.resSort.eval ψ) (consList ts ρ)
              [((((pk m).dsF 0 ψ).drop q.nP).map (·.2.2)) ++ [idxEqAV []]]) := by
    intro m cA hm hcs hnIdx0 ψ ρ ts hsp
    have hcA : (ctorsAs.getD m [])[0]? = some cA := by rw [hcs]; rfl
    have hlenA : (ctorsAs.getD m []).length = 1 := by rw [hcs]; rfl
    have hIds0 : ((ppsOf m ψ).drop q.nP).map (·.2.2) = [] := by
      refine List.length_eq_zero_iff.mp ?_
      rw [hIdsLen m ψ, hnIdx0]
    have hEss0 : (blockDataOf V q ctorsAs pk uOf ppsOf).Ess m ψ = [[]] := by
      obtain ⟨Es, hEs⟩ := List.length_eq_one_iff.mp (by
        show (essOfR _).length = 1
        rw [essOfR_length]
        exact (fixCtorDataList_length _ _ _ _ _ _ _ _).trans hlenA :
          ((blockDataOf V q ctorsAs pk uOf ppsOf).Ess m ψ).length = 1)
      have hE0 : Es = (pk m).esF 0 ψ := by
        have h := hEssRD m 0 cA ψ hcA
        rwa [hEs] at h
      have hlen0 : ((pk m).esF 0 ψ).length = 0 := by
        have h := (hpk m hm 0 cA hcA).lenE ψ
        rwa [hnIdx0] at h
      rw [hEs, hE0, List.length_eq_zero_iff.mp hlen0]
    have hFss1 : (blockDataOf V q ctorsAs pk uOf ppsOf).Fss m ψ
        = [((((pk m).dsF 0 ψ).drop q.nP).map (·.2.2))] := by
      obtain ⟨Fs, hFs⟩ := List.length_eq_one_iff.mp (by
        show (fssOfR _ _).length = 1
        rw [fssOfR_length]
        exact (fixCtorDataList_length _ _ _ _ _ _ _ _).trans hlenA :
          ((blockDataOf V q ctorsAs pk uOf ppsOf).Fss m ψ).length = 1)
      have h0 := hFssRD m 0 cA ψ hcA
      rw [hFs] at h0 ⊢
      simp only [List.getD_cons_zero] at h0
      rw [h0]
    have h := blockHoleFold_params (A := blockLeafH (blockDataOf V q ctorsAs pk uOf ppsOf))
      hHR rfl (ψ := ψ) (fun _ _ => rfl) (fun c hc => hSC.lenPps c ψ hc) hm hIds0
      (fun ρp hs => fun c hc => (hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
        (hρpOf ψ ρp 0 hk0 hs c hc)).1)
      (fun ρp hs => hSC.holeOk ψ ρp hs) (hSC.holeFun ψ)
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
        shapeT := ?_
        resT := ?_
        resR := ?_
        resC := ?_
        leqF := ?_
        boundF := ?_
        dsLen := ?_
        dsBelow := ?_
        foldT := ?_
        noProjT := ?_
        noProjC := ?_
        noProjB := ?_
        sortsF := ?_ }
    · -- etaData
      intro m cA hm hcs he
      have hcs' : ctorsAs.getD m [] = [cA] := hcs
      have hcA : (ctorsAs.getD m [])[0]? = some cA := by rw [hcs']; rfl
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      obtain ⟨c, hcsM, hcaps⟩ | hcaps := blockCapsAt_cases q m isRec
      case inr => rw [hcaps] at he; exact nomatch he
      obtain ⟨c', -, hc0, hname, hnF, -⟩ := (hfacts m cvTa hm hcv).2 0 cA hcA
      rw [hcsM] at hc0
      obtain rfl : c = c' := by simpa using hc0
      rw [hcaps] at he ⊢
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at he
      refine ⟨?_, hname.symm, rfl, hnF.symm⟩
      show (Level.isEquiv q.resSort .zero == some true) = false
      rw [← hProp]; exact he.1.2
    · -- stripC
      intro m cA hm hcs
      have hcs' : ctorsAs.getD m [] = [cA] := hcs
      have hcA : (ctorsAs.getD m [])[0]? = some cA := by rw [hcs']; rfl
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hstrip, -⟩ := (hfacts m cvTa hm hcv).2 0 cA hcA
      exact hstrip
    · -- shapeT
      intro m hm
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      rw [show (blockDataOf V q ctorsAs pk uOf ppsOf).memberName m = cvTa.name from
        (hF.nameOf m cvTa hcv).symm]
      exact hF.pshapeOf m cvTa hcv
    · -- resT
      intro m hm
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      rw [show (blockDataOf V q ctorsAs pk uOf ppsOf).memberName m = cvTa.name from
        (hF.nameOf m cvTa hcv).symm]
      exact hF.nresOf m cvTa hcv
    · -- resR: a member's recursor name is reserved only if the member's is
      intro m hm
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      rw [show (blockDataOf V q ctorsAs pk uOf ppsOf).memberName m = cvTa.name from
        (hF.nameOf m cvTa hcv).symm]
      exact reservedBasisNames_str_rec (hF.nresOf m cvTa hcv)
    · -- resC
      intro m cA hm hcs
      have hcs' : ctorsAs.getD m [] = [cA] := hcs
      have hcA : (ctorsAs.getD m [])[0]? = some cA := by rw [hcs']; rfl
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      obtain ⟨-, -, -, -, -, -, -, -, -, hres, -⟩ := (hfacts m cvTa hm hcv).2 0 cA hcA
      exact hres
    · -- leqF
      intro m cA hm hcs i hi hnp
      have hcs' : ctorsAs.getD m [] = [cA] := hcs
      have hcA : (ctorsAs.getD m [])[0]? = some cA := by rw [hcs']; rfl
      obtain ⟨sorts, hsj, -, hleq, -⟩ := hsortsAt m hm 0 cA hcA
      rw [show (sortsss.getD m []).getD 0 [] = sorts from by
        rw [List.getD_eq_getElem?_getD, hsj]; rfl]
      exact hleq i hi hnp
    · -- boundF
      intro m cA hm hcs ψ ρ hρ hnp
      have hcs' : ctorsAs.getD m [] = [cA] := hcs
      have hcA : (ctorsAs.getD m [])[0]? = some cA := by rw [hcs']; rfl
      exact ((hframes m hm 0 cA hcA).2 ψ ρ hρ).2.2.1 hnp
    · -- dsLen
      intro m j cA hm hj ψ
      exact (hpk m hm j cA hj).len ψ
    · -- dsBelow
      intro m j cA hm hj ψ
      exact (hpk m hm j cA hj).below ψ
    · -- foldT
      intro m cA hm hcs hnIdx0 ψ ρ ts hsp
      exact hfoldT m cA hm hcs hnIdx0 ψ ρ ts hsp
    · -- noProjT: a stored former's type resolves before the block, where
      -- no member is stored
      intro m c cvTb hm hc i
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      rw [show (blockDataOf V q ctorsAs pk uOf ppsOf).memberName m = cvTa.name from
        (hF.nameOf m cvTa hcv).symm]
      exact ConLeche.Expr.noProjAt_of_constsResolve (hF.freshOf m cvTa hcv) _
        (hF.resolveOf c cvTb hc)
    · -- noProjC: an annotated constructor type carries a projection only
      -- where a table entry typed it, and no member's table is stored yet
      intro m c j cA hm hm1 hm2 hj i
      have hck : c < q.k := hctorLt c j cA hj
      obtain ⟨cvTa, hcv⟩ := hcvOf c hck
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨ty₀, hfv₀, hann₀⟩, -⟩ :=
        (hfacts c cvTa hck hcv).2 j cA hj
      exact ConLeche.annotateCore_noProjAt μ hann₀ hfv₀
        (ConLeche.Env.findProj?_none_of_fresh (hprojTbl' m hm hm1 hm2) i)
    · -- noProjB: member c's table bodies carry c's OWN projections only
      intro m c cA bodies hm hm1 hm2 hck hcm hcs hbodies i j
      have hcs' : ctorsAs.getD c [] = [cA] := hcs
      have hcA : (ctorsAs.getD c [])[0]? = some cA := by rw [hcs']; rfl
      obtain ⟨cvTa, hcv⟩ := hcvOf c hck
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨ty₀, hfv₀, hann₀⟩, -⟩ :=
        (hfacts c cvTa hck hcv).2 0 cA hcA
      have hnoC : ConLeche.Expr.NoProjAt
          ((blockDataOf V q ctorsAs pk uOf ppsOf).memberName m) i cA.1.type :=
        ConLeche.annotateCore_noProjAt μ hann₀ hfv₀
          (ConLeche.Env.findProj?_none_of_fresh (hprojTbl' m hm hm1 hm2) i)
      refine ConLeche.noProjAt_structProjBodies (fun j' => ?_) hbodies hnoC j
      rintro ⟨hh, -⟩
      exact hmnameNe' c m hck hm hcm hh
    · -- sortsF
      intro m cA hm hcs ψ ρ hρ j hj as hsp
      have hcs' : ctorsAs.getD m [] = [cA] := hcs
      have hcA : (ctorsAs.getD m [])[0]? = some cA := by rw [hcs']; rfl
      obtain ⟨sorts, hsj, -, -, hsf⟩ := hsortsAt m hm 0 cA hcA
      rw [show (sortsss.getD m []).getD 0 [] = sorts from by
        rw [List.getD_eq_getElem?_getD, hsj]; rfl]
      exact hsf ψ ρ hρ j hj as hsp
  · -- the block's η invariant at the formers' environment
    refine ⟨hEclR, ?_⟩
    rw [hcons]
    refine ConLeche.blockEtaInv_snd_consBlockInds (fun T' hT' => ?_) (fun j cvTa hj => ?_)
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hT'
      obtain ⟨cvTb, hcv⟩ : ∃ cvTb, cvTas[j]? = some cvTb :=
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
        have := (List.getElem?_eq_some_iff.mp hj).1; rw [hF.lenCv] at this; exact this
      refine ⟨q.members[j], List.getElem?_eq_getElem hjk, ?_⟩
      rw [hF.nameOf j cvTa hj, ConLeche.BlockShape.memberNames, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_getElem hjk]
      rfl
  · -- every member's constructors are fresh at the formers' environment
    intro c j cA hj
    have hck : c < q.k := hctorLt c j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf c hck
    obtain ⟨-, -, -, -, -, -, hfresh, -⟩ := (hfacts c cvTa hck hcv).2 j cA hj
    exact hfresh


end ConLeche.Model
