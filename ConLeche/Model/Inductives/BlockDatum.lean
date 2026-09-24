module

public import ConLeche.Model.Inductives.BlockAssembly
public import ConLeche.Model.Inductives.BlockStageTables
import ConLeche.Model.Inductives.BlockCaps
import ConLeche.Verify.Inductives.BlockInv
public import ConLeche.Verify.Inductives.BlockWF
public section

/-!
# The block's representation datum, built from the install's run (task #315 M3)

`declNative`'s `DeclNative.lean:120–560` at `k` members, one stage at
a time: the formers' run (`blockFormerFacts_of`), the DUMMY pass
(`blockDummyPass`), every member's constructors read at its carrier
(`blockCtorFunsAt`), the members' index telescopes
(`blockIdxFacts_of`), the operator's premise bundle at the leaves'
chains (`blockChainsOk_of`), the REAL pass (`blockRealPass`), the
constructors read again at ITS carrier and identified with the dummy
ones off the recursive fields (`blockCtorDataI_ident`) — and out of
that the record `BlockData` the stages are stated over.

**The record is a `def`, not a choice.**  `blockDataOf` is the datum
at chosen per-member constructor data (`BlockMemberPick`), a parameter
count and a telescope reading; every shape equation the later stages
need (`d.nP = q.nP`, `d.rss`, `d.tgtss`, …) is then definitional, and
the two carriers differ only in the pick.  `BlockData.withPhi`
installs the tuple operator and the injections over the record's own
derived fields, so `blockModelAt_of_stages`' `hPhi`/`hinj` are `rfl`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind BlockFieldKind IndCaps
  BlockShape BlockParts MemberShape BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The record -/

/-- **The block's representation record but for the operator and the
injections**, at a chosen per-member constructor pick. -/
@[expose] noncomputable def blockDataPre (V : Type w) [SetTheory V] (q : BlockShape) (env : Env)
    (ctorsAs : List (List (ConstantVal × Nat)))
    (kinds : List (List (List BlockFieldKind))) (pk : Nat → BlockMemberPick)
    (uOf : Nat → (Name → Nat) → Nat)
    (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) : BlockData V where
  nP := q.nP
  k := q.k
  nInst := 0
  resSort := q.resSort
  isProp := q.isProp
  large := q.large
  env₀ := env
  memberNames := q.memberNames
  nIdxs := q.nIdxs
  ppsM := ppsOf
  uM := uOf
  ctorsM := fun c => ctorsAs.getD c []
  idxF := fun c j => (pk c).idxF j
  dsF := fun c j => (pk c).dsF j
  esF := fun c j => (pk c).esF j
  srcsF := fun c j => (pk c).srcsF j
  ksF := fun c j => ((kinds.getD c []).getD j []).map ConLeche.BlockFieldKind.toRec
  tgts := fun c j i => (ConLeche.blockTgtsOf ((kinds.getD c []).getD j [])).getD i 0
  fvsPF := fun c j => (pk c).fvsPF j
  xFvsF := fun c j => (pk c).xFvsF j
  xrestF := fun c j => (pk c).xrestF j
  eissF := fun c j => (pk c).eissF j
  tssF := fun c j => (pk c).tssF j
  Φ := fun _ _ X => X
  inj := fun _ _ _ _ => SetTheory.pt

/-- **The tuple operator and the injections, over the record's own
derived fields**: the fixpoint route's operator at the block's width,
and the tagged-union injections, the point at a `Prop`-valued
block. -/
@[expose] noncomputable def BlockData.withPhi (d : BlockData V) : BlockData V :=
  { d with
    Φ := fun ψ ρp => blockPhi d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
      d.rss d.tgtss (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fun c => d.Fss c ψ)
      (fun c => d.Ess c ψ)
    inj := fun ψ _ j fs =>
      if d.w ψ = 0 then (SetTheory.pt : V) else ConLeche.SetTheory.Tower.inj j (mkTower (fs ++ [SetTheory.pt])) }

/-- **The block's representation record**, at a pick. -/
@[expose] noncomputable def blockDataOf (V : Type w) [SetTheory V] (q : BlockShape) (env : Env)
    (ctorsAs : List (List (ConstantVal × Nat)))
    (kinds : List (List (List BlockFieldKind))) (pk : Nat → BlockMemberPick)
    (uOf : Nat → (Name → Nat) → Nat)
    (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) : BlockData V :=
  (blockDataPre V q env ctorsAs kinds pk uOf ppsOf).withPhi

/-- **A member's fixpoint leaf**, over the record's own chains but for
the field domains, which are the DUMMY former's (`fssZ`): that is what
the members' formers are consed with, and what
`BlockCtorsStage.leaf` names. -/
@[expose] noncomputable def blockLeafZ (d : BlockData V)
    (fssZ : (Name → Nat) → Nat → List (List AnnotTerm)) (c : Nat) (ψ : Name → Nat) :
    AnnotTerm :=
  blockTyAV d.k (d.w ψ) (fun c' => d.uM c' ψ) (fun c' => d.IdsM c' ψ) d.rss d.tgtss
    (fun c' => d.tlss c' ψ) (fun c' => d.Eiss c' ψ) (fssZ ψ) (fun c' => d.Ess c' ψ)
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
theorem blockCtorRuns_of {ctx : ConLeche.NestCtx} {envI : Env} {q : BlockShape} {F : Nat}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {sortsss : List (List (List Level))}
    (hCtors : ConLeche.checkBlockCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI envI q ctx
      (q.members.zip cvTas) = .ok (ctorsAs, sortsss))
    (hnameOf : ∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
      cvTb.name = q.memberNames.getD j .anonymous) :
    ∀ (m : Nat) (cvTa : ConstantVal), m < q.k → cvTas[m]? = some cvTa →
      ConLeche.checkSumCtors (ConLeche.fueledOps μ F) envI envI ctx cvTa.name q.lps q.nP
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

/-- **One member's constructors, as stored**: `declNative`'s `hrunOf`
at a block member. -/
theorem blockCtorFacts_of {ctx : ConLeche.NestCtx} {envI : Env} {q : BlockShape} {F : Nat} {cvTa : ConstantVal} {m : Nat}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hrun : ConLeche.checkSumCtors (ConLeche.fueledOps μ F) envI envI ctx cvTa.name q.lps q.nP
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
        ConLeche.checkSumCtor (ConLeche.fueledOps μ F) envI envI ctx cvTa.name q.lps q.nP
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
theorem blockEtaSide_of {ctx : ConLeche.NestCtx} {env envI : Env} {q : BlockShape} {F : Nat} {isRec : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {sortsss : List (List (List Level))}
    (hcons : envI = ConLeche.consBlockInds q isRec cvTas 0 env)
    (hlenCv : cvTas.length = q.k)
    (hnameOf : ∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
      cvTb.name = q.memberNames.getD j .anonymous)
    (hCtors : ConLeche.checkBlockCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI envI q ctx
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

/-! ## Kit: the chains' bounds, the targets, the zero fold -/

/-- **A member's X-chains are closed** under the parameters, the family
tuple and the index tuple (`chainsXI_below_of` at `k` members). -/
theorem chainsXBI_below_of {nP nIdx n : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
    {rss : List (List Bool)} {tgtss : List (List Nat)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Ess : List (List AnnotTerm)}
    (hIds : ∀ c, FieldsBelow nP (Idss c)) (hlenF : Fss.length = n)
    (hTls : ∀ j, j < n → ∀ i, DomsBelow (nP + i) ((tlss.getD j []).getD i []))
    (hEis : ∀ j, j < n → ∀ i, ∀ E ∈ (Eiss.getD j []).getD i [],
      Term.bvarsBelow (nP + i + ((tlss.getD j []).getD i []).length) E.erase)
    (hFs : ∀ j, j < n → FieldsBelow nP (Fss.getD j []))
    (hEsLen : ∀ j, j < n → (Ess.getD j []).length = nIdx)
    (hEs : ∀ j, j < n → ∀ E ∈ Ess.getD j [],
      Term.bvarsBelow (nP + (Fss.getD j []).length) E.erase) :
    ∀ chain ∈ chainsXBI uf Idss nIdx rss tgtss tlss Eiss Fss Ess,
      FieldsBelow (nP + 2) chain := by
  intro chain hc
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  rw [chainsXBI_getElem?] at hj
  split at hj
  · next hjF =>
    obtain rfl := Option.some.inj hj
    have hjn : j < n := by omega
    exact chainXBI_below hIds (hTls j hjn) (hEis j hjn) (hFs j hjn) (hEsLen j hjn) (hEs j hjn)
  · exact nomatch hj

/-- **The real chains of a member with ONE fieldless constructor** are
the leaf's (`chainsRealI_zero` at a block member). -/
theorem chainsRealBI_zero {k w m : Nat} {mu : Nat → V} {ρp : Nat → V} {uf : Nat → Nat}
    {Idss : Nat → List AnnotTerm} {rss : List (List Bool)} {tgtss : List (List Nat)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    (hIds : Idss m = []) :
    ChainsRealBI mu k w ρp uf Idss m rss tgtss tlss Eiss [[]] [[]] [[]] := by
  refine ⟨rfl, rfl, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · simp only [List.length_singleton] at hj
    obtain rfl : j = 0 := by omega
    rw [hIds]; rfl
  · simp only [List.length_singleton] at hj
    obtain rfl : j = 0 := by omega
    rfl
  · simp only [List.length_singleton] at hj
    obtain rfl : j = 0 := by omega
    trivial

/-! ## The constructors' stage, from the run -/

set_option maxHeartbeats 1600000 in
/-- **The block's representation record and the constructors' stage's
obligation, from the install's run** — `declNative`'s
`DeclNative.lean:120–560` at `k` members.  The two former passes
(`blockDummyPass`, `blockRealPass`) around the members' constructor
readings (`blockCtorFunsAt`) and the operator's premise bundle at the
leaves' chains (`blockChainsOk_of`); the record is `blockDataOf` at
the REAL pick, and the dummy readings survive in it only through
`fssZ` and the identification off the recursive fields
(`blockCtorDataI_ident`). -/
theorem blockTablesStage_of {ctx : ConLeche.NestCtx} (hμ : μ.verifiedChecks = true) {F : Nat} {env envI : Env}
    {p₀ : BlockParts} {isRec : Bool} {cvTas : List ConstantVal} {q : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    {kinds : List (List (List ConLeche.BlockFieldKind))} {isorts : List (List Level)}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hlps₀ : ∀ ms ∈ p₀.members, ms.cvT.levelParams = p₀.lps)
    (hndM : q.memberNames.Nodup)
    (hndC : (q.allCtors.map (·.1.name)).Nodup)
    (hClps : ∀ c ∈ q.allCtors, c.1.levelParams = q.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false)
    (hInd : ConLeche.checkBlockInds (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p₀ isRec
      = .ok (envI, cvTas, q))
    (hCtors : ConLeche.checkBlockCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI envI q ctx
      (q.members.zip cvTas) = .ok (ctorsAs, sortsss))
    (hK : ConLeche.classifyBlockKinds (m := ConLeche.CheckM) q.memberNames q.lps q.nP q.nIdxs
      ctorsAs = .ok kinds)
    (hsorts : ConLeche.checkBlockIdxSorts (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI q
      (q.members.zip cvTas) = .ok isorts)
    (hFOk : ConLeche.blockFieldsOk env q.memberNames q.lps q.nP q.nIdxs ctorsAs kinds = true)
    (hfamFree : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < q.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (q.members.getD m default).nIdx = 0 → 0 < cA.2 →
      envI.find? (projFnName (q.memberNames.getD m .anonymous) 0) = none)
    (hprojTbl : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < q.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (q.members.getD m default).nIdx = 0 →
      envI.find? (projTableName (q.memberNames.getD m .anonymous)) = none) :
    ∃ (pk : Nat → BlockMemberPick) (uOf : Nat → (Name → Nat) → Nat)
      (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (fssZ : (Name → Nat) → Nat → List (List AnnotTerm)) (mpI : EnvModelM V μ envI),
      BlockNamesOk (V := V) (blockDataOf V q env ctorsAs kinds pk uOf ppsOf) cvTas ∧
      BlockTablesStage (V := V) μ F (blockDataOf V q env ctorsAs kinds pk uOf ppsOf) q.lps cvTas
        q isRec (blockLeafZ (blockDataOf V q env ctorsAs kinds pk uOf ppsOf) fssZ) fssZ envI
        q.ctorNamesAt (fun m => (sortsss.getD m []).getD 0 []) ∧
      BlockCtorsCore mpI.base2 (blockDataOf V q env ctorsAs kinds pk uOf ppsOf) q.lps cvTas
        q isRec (blockLeafZ (blockDataOf V q env ctorsAs kinds pk uOf ppsOf) fssZ) 0 ∧
      ConLeche.BlockEtaInv envI q.memberNames q.ctorNamesAt ∧
      ∀ (c j : Nat) (cA : ConstantVal × Nat),
        ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).ctorsM c)[j]? = some cA →
        envI.find? cA.1.name = none := by
  classical
  -- the run's shape: the k formers consed at once
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, hmem0, -, hq, hcons, -, -, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  have hqm : q.members = p₀.members := by rw [hq]; rfl
  have hne : 0 < q.members.length := by rw [hqm, hmem0]; simp
  have hnames0 : q.memberNames ≠ [] := by
    intro hh
    have : q.memberNames.length = q.members.length := by
      show (q.members.map _).length = _; simp
    rw [hh] at this; simp at this; omega
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
  -- the kinds, positionally (their count); the targets they carry are
  -- read off the re-check below
  obtain ⟨hlenK, -⟩ := ConLeche.classifyBlockKinds_inv hK
  -- conjunct 7 at one member
  obtain ⟨-, hFOkm'⟩ := ConLeche.blockFieldsOk_inv hFOk
  have hFOkm : ∀ m, m < q.k →
      ConLeche.blockMemberFieldsOk env q.memberNames q.lps q.nP q.nIdxs (ctorsAs.getD m [])
        (kinds.getD m []) = true := by
    intro m hm
    obtain ⟨kss, hkss, hok⟩ := hFOkm' m (ctorsAs.getD m []) (hCA m hm)
    have hgd : kinds.getD m [] = kss := by
      rw [List.getD_eq_getElem?_getD, hkss]; rfl
    rw [hgd]; exact hok
  have htgtLt : ∀ (m : Nat), m < q.k → ∀ j i : Nat,
      (ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).getD i 0 < q.memberNames.length :=
    -- the target bound, off the RE-CHECK (conjunct 7), not the classifier
    fun m hm j i => ConLeche.blockMemberFieldsOk_tgtsOf_lt hnames0 (hFOkm m hm) j i
  have htgtLtK : ∀ (m : Nat), m < q.k → ∀ j i : Nat,
      (ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).getD i 0 < q.k := by
    intro m hm j i
    have h := htgtLt m hm j i
    rw [hlenN] at h
    exact h
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
          ConLeche.checkSumCtor (ConLeche.fueledOps μ F) envI envI ctx cvTa.name q.lps q.nP
            (q.nIdxs.getD m 0) q.resSort q.isProp q.large c.1 cA.2 cvTa = .ok (cA.1, sorts) :=
    fun m cvTa hm hcv =>
      blockCtorFacts_of (blockCtorRuns_of hCtors hF.nameOf m cvTa hm hcv)
        (fun c hc => hClps c (hmemCtors m hm c hc))
  -- ## the DUMMY pass: the k formers at the EMPTY chain lists
  obtain ⟨mpD, hEclD, hFDD, hfindD, hagD⟩ := blockDummyPass mp hInd hF hndM hE hetaNe hetaFresh
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
        BlockCtorDataI mp'.base2 env (q.memberNames.getD m .anonymous)
          (fun i => q.memberNames.getD
            ((ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).getD i 0) .anonymous)
          (fun i => q.nIdxs.getD
            ((ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).getD i 0) 0)
          q.lps cA.1 q.nP cA.2 (q.nIdxs.getD m 0) q.resSort q.isProp q.large
          (pk.idxF j) (pk.dsF j) (pk.esF j) (pk.srcsF j)
          (((kinds.getD m []).getD j []).map ConLeche.BlockFieldKind.toRec)
          (pk.fvsPF j) (pk.xFvsF j) (pk.xrestF j) (pk.eissF j) (pk.tssF j) := by
    intro mp' hfind m
    by_cases hm : m < q.k
    · obtain ⟨cvTa, hcv⟩ : ∃ cvTa, cvTas[m]? = some cvTa :=
        ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact hm)⟩
      obtain ⟨pk, hpk⟩ := blockCtorFunsAt hμ mp' hcv hF.lenCv hne hF.nameOf hF.lpsOf hF.sEval
        hF.stripOf hfind (hFOkm m hm) (htgtLt m hm)
        (fun j cA hj => by
          obtain ⟨c, sorts, -, -, -, -, -, -, -, -, -, -, -, hCtor⟩ :=
            (hfacts m cvTa hm hcv).2 j cA hj
          exact ⟨c, sorts, hCtor⟩)
      exact ⟨pk, fun _ => hpk⟩
    · exact ⟨⟨fun _ => [], fun _ _ => [], fun _ _ => [], fun _ => [], fun _ => [], fun _ => [],
        fun _ => .bvar 0, fun _ _ => [], fun _ _ => []⟩, fun hh => absurd hh hm⟩
  obtain ⟨pk₀, hpk₀⟩ : ∃ pk₀ : Nat → BlockMemberPick, ∀ m : Nat, m < q.k →
      ∀ (j : Nat) (cA : ConstantVal × Nat), (ctorsAs.getD m [])[j]? = some cA →
        BlockCtorDataI mpD.base2 env (q.memberNames.getD m .anonymous)
          (fun i => q.memberNames.getD
            ((ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).getD i 0) .anonymous)
          (fun i => q.nIdxs.getD
            ((ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).getD i 0) 0)
          q.lps cA.1 q.nP cA.2 (q.nIdxs.getD m 0) q.resSort q.isProp q.large
          ((pk₀ m).idxF j) ((pk₀ m).dsF j) ((pk₀ m).esF j) ((pk₀ m).srcsF j)
          (((kinds.getD m []).getD j []).map ConLeche.BlockFieldKind.toRec)
          ((pk₀ m).fvsPF j) ((pk₀ m).xFvsF j) ((pk₀ m).xrestF j) ((pk₀ m).eissF j)
          ((pk₀ m).tssF j) :=
    ⟨fun m => (hpickOf mpD (fun j cvTb hj => (hfindD j cvTb hj).1) m).choose,
      fun m => (hpickOf mpD (fun j cvTb hj => (hfindD j cvTb hj).1) m).choose_spec⟩
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
  -- ## the chain facts at a carrier holding the k formers, per member
  -- and constructor (used at BOTH passes' carriers)
  have hchainsAt : ∀ (mp' : EnvModelM V μ envI) (pk' : Nat → BlockMemberPick),
      (∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
        envI.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt q j isRec))) →
      (∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
        FormerData mp'.base2 cvTb (q.nP + q.nIdxs.getD j 0) q.resSort (ppsOf j)) →
      (∀ (t : Nat), t < q.k → ∀ ψ : Name → Nat, ∃ B,
        mp'.base2.acval (q.memberNames.getD t .anonymous) ψ
          = mkLamsC (q.resSort.eval ψ + 1) (ppsOf t ψ) B) →
      (∀ (m : Nat), m < q.k → ∀ (j : Nat) (cA : ConstantVal × Nat),
        (ctorsAs.getD m [])[j]? = some cA →
        BlockCtorDataI mp'.base2 env (q.memberNames.getD m .anonymous)
          (fun i => q.memberNames.getD
            ((ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).getD i 0) .anonymous)
          (fun i => q.nIdxs.getD
            ((ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).getD i 0) 0)
          q.lps cA.1 q.nP cA.2 (q.nIdxs.getD m 0) q.resSort q.isProp q.large
          ((pk' m).idxF j) ((pk' m).dsF j) ((pk' m).esF j) ((pk' m).srcsF j)
          (((kinds.getD m []).getD j []).map ConLeche.BlockFieldKind.toRec)
          ((pk' m).fvsPF j) ((pk' m).xFvsF j) ((pk' m).xrestF j) ((pk' m).eissF j)
          ((pk' m).tssF j)) →
      ∀ (m : Nat), m < q.k → ∀ (j : Nat) (cA : ConstantVal × Nat),
      (ctorsAs.getD m [])[j]? = some cA → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsOf m ψ).take q.nP).map (·.2.2)).reverse ρp →
      ChainFactsB q.k (q.resSort.eval ψ) q.nP cA.2 ρp (fun c => uOf c ψ)
          (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) m
          (((kinds.getD m []).getD j []).map ConLeche.BlockFieldKind.toRec)
          (ConLeche.blockTgtsOf ((kinds.getD m []).getD j []))
          ((pk' m).tssF j ψ) ((((pk' m).dsF j ψ).drop q.nP).map (·.2.2))
          ((pk' m).eissF j ψ) ((pk' m).esF j ψ) ∧
      ChainValidFacts q.nP cA.2 ρp
          (((kinds.getD m []).getD j []).map ConLeche.BlockFieldKind.toRec)
          ((pk' m).tssF j ψ) ((((pk' m).dsF j ψ).drop q.nP).map (·.2.2))
          ((pk' m).eissF j ψ) ((pk' m).esF j ψ) := by
    intro mp' pk' hfind' hFD' hleaf' hpk' m hm j cA hj ψ ρp hρp
    obtain ⟨cvTa, hcv⟩ := hcvOf m hm
    obtain ⟨c, sorts, -, -, -, -, -, -, -, -, -, -, -, hCtor⟩ := (hfacts m cvTa hm hcv).2 j cA hj
    have hTname : cvTa.name = q.memberNames.getD m .anonymous := hF.nameOf m cvTa hcv
    have hfT : envI.find? (q.memberNames.getD m .anonymous)
        = some (.indInfo cvTa (ConLeche.blockCapsAt q m isRec)) := by
      rw [← hTname]; exact hfind' m cvTa hcv
    have hFDm : FormerData mp'.base2 cvTa (q.nP + q.nIdxs.getD m 0) q.resSort (ppsOf m) :=
      hFD' m cvTa hcv
    have hD := hpk' m hm j cA hj
    rw [hTname] at hCtor
    refine ⟨?_, blockChainValidFacts_of hμ mp' hCtor hfT hProp' hFDm (hleaf' m hm) hD ψ ρp hρp⟩
    refine blockChainFacts_of (k := q.k) (m := m) hμ mp' hCtor hfT hProp' hFDm (hleaf' m hm) hD
      ψ ρp
      (ppsOf := fun i ψ' =>
        ppsOf ((ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).getD i 0) ψ')
      (fun i ψ' => hlenPpsOf _ (htgtLtK m hm j i) ψ')
      (fun i ψ' => hleaf' _ (htgtLtK m hm j i) ψ')
      (fun i _ _ => htgtLtK m hm j i)
      (fun _ _ _ => rfl) rfl hρp
  have hCD := hchainsAt mpD pk₀ (fun j cvTb hj => (hfindD j cvTb hj).1) hFDD hleafOfD hpk₀
  -- ## the DUMMY record: the field lists the members' leaves are built over
  let dZ : BlockData V := blockDataOf V q env ctorsAs kinds pk₀ uOf ppsOf
  have hrangeGetD : ∀ L : List Nat, (List.range L.length).map (fun i => L.getD i 0) = L := by
    intro L
    refine List.ext_getElem (by simp) (fun i h1 h2 => ?_)
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2]
    rfl
  have htgtssEq : ∀ (m j : Nat), j < (ctorsAs.getD m []).length →
      (dZ.tgtss m).getD j [] = ConLeche.blockTgtsOf ((kinds.getD m []).getD j []) := by
    intro m j hj
    show ((List.range (ctorsAs.getD m []).length).map fun j' =>
      (List.range (((kinds.getD m []).getD j' []).map ConLeche.BlockFieldKind.toRec).length).map
        fun i => (ConLeche.blockTgtsOf ((kinds.getD m []).getD j' [])).getD i 0).getD j [] = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    show (List.range (((kinds.getD m []).getD j []).map _).length).map _ = _
    rw [List.length_map,
      show ((kinds.getD m []).getD j []).length
        = (ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).length from by
          show _ = (List.map _ _).length; rw [List.length_map]]
    exact hrangeGetD _
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
  have hTlssZD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (ctorsAs.getD m [])[j]? = some cA → (dZ.tlss m ψ).getD j [] = (pk₀ m).tssF j ψ :=
    fun _ _ _ _ hj => tlssOfR_fixCtorDataList_getD hj
  have hEissZD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (ctorsAs.getD m [])[j]? = some cA → (dZ.Eiss m ψ).getD j [] = (pk₀ m).eissF j ψ :=
    fun _ _ _ _ hj => eissOfR_fixCtorDataList_getD hj
  have hlenFsZ : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      m < q.k → (ctorsAs.getD m [])[j]? = some cA →
      ((dZ.Fss m ψ).getD j []).length = cA.2 := by
    intro m j cA ψ hm hj
    rw [hFssZD m j cA ψ hj]
    simp [(hpk₀ m hm j cA hj).len ψ]
  -- ## the block operator's premise bundle, at the LEAVES' chains
  have hbundle : ∀ (ψ : Name → Nat) (ρp : Nat → V) (m : Nat), m < q.k →
      Sat V (((ppsOf m ψ).take q.nP).map (·.2.2)).reverse ρp →
      BlockChainsOk dZ.k (dZ.w ψ) ρp (fun c => dZ.uM c ψ) (fun c => dZ.IdsM c ψ) dZ.rss
        dZ.tgtss (fun c => dZ.tlss c ψ) (fun c => dZ.Eiss c ψ) (fun c => dZ.Fss c ψ)
        (fun c => dZ.Ess c ψ) ∧
      ∀ Y, Y ∈ˢ famsSpaceB dZ.k (dZ.w ψ) ρp (fun c => dZ.uM c ψ) (fun c => dZ.IdsM c ψ) →
        ∀ c, c < dZ.k → ∀ t, t ∈ˢ idxSet (dZ.uM c ψ) ρp (dZ.IdsM c ψ) →
        SumFieldsValid (cons t (cons Y ρp))
          (chainsXBI (fun c' => dZ.uM c' ψ) (fun c' => dZ.IdsM c' ψ) (dZ.IdsM c ψ).length
            (dZ.rss c) (dZ.tgtss c) (dZ.tlss c ψ) (dZ.Eiss c ψ) (dZ.Fss c ψ) (dZ.Ess c ψ)) := by
    intro ψ ρp m hm hρp
    refine blockChainsOk_of (nP := q.nP) (nOf := fun c => (ctorsAs.getD c []).length)
      (ksF := dZ.ksF)
      (fun c hc => (hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
        (hρpOf ψ ρp m hm hρp c hc)).1)
      (fun c hc => (hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
        (hρpOf ψ ρp m hm hρp c hc)).2)
      (fun c _ => hlenFssZ c ψ) (fun c _ j hj => rssOfK_getD hj) ?_ ?_
    · intro c hc j hj
      obtain ⟨cA, hjA⟩ : ∃ cA, (ctorsAs.getD c [])[j]? = some cA :=
        ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hlenFsZ c j cA ψ hc hjA, hFssZD c j cA ψ hjA, hEssZD c j cA ψ hjA,
        hEissZD c j cA ψ hjA, hTlssZD c j cA ψ hjA, htgtssEq c j hj]
      exact (hCD c hc j cA hjA ψ ρp (hρpOf ψ ρp m hm hρp c hc)).1
    · intro c hc j hj
      obtain ⟨cA, hjA⟩ : ∃ cA, (ctorsAs.getD c [])[j]? = some cA :=
        ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hlenFsZ c j cA ψ hc hjA, hFssZD c j cA ψ hjA, hEssZD c j cA ψ hjA,
        hEissZD c j cA ψ hjA, hTlssZD c j cA ψ hjA]
      exact (hCD c hc j cA hjA ψ ρp (hρpOf ψ ρp m hm hρp c hc)).2
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
      exact ⟨h1, h2, hD.eissParams ψ₁ ψ₂ hφ', hD.tssParams ψ₁ ψ₂ hφ'⟩
    · have hnil : ctorsAs.getD c [] = [] := getD_of_le [] (by rw [hlenCtorsAs]; omega)
      show fixCtorDataList _ _ _ _ _ _ (ctorsAs.getD c []) 0
        = fixCtorDataList _ _ _ _ _ _ (ctorsAs.getD c []) 0
      rw [hnil]
      rfl
  have hZparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ n ∈ q.lps, ψ₁ n = ψ₂ n) →
      (∀ c, uOf c ψ₁ = uOf c ψ₂) ∧ (∀ c, dZ.tlss c ψ₁ = dZ.tlss c ψ₂) ∧
      (∀ c, dZ.Eiss c ψ₁ = dZ.Eiss c ψ₂) ∧
      (fun c => dZ.Fss c ψ₁) = (fun c => dZ.Fss c ψ₂) ∧
      (∀ c, dZ.Ess c ψ₁ = dZ.Ess c ψ₂) := by
    intro ψ₁ ψ₂ hφ
    refine ⟨fun c => hUparams c ψ₁ ψ₂ hφ, fun c => ?_, fun c => ?_, funext fun c => ?_,
      fun c => ?_⟩
    · show tlssOfR _ = tlssOfR _; rw [hcdsParams c ψ₁ ψ₂ hφ]
    · show eissOfR _ = eissOfR _; rw [hcdsParams c ψ₁ ψ₂ hφ]
    · show fssOfR _ _ = fssOfR _ _; rw [hcdsParams c ψ₁ ψ₂ hφ]
    · show essOfR _ = essOfR _; rw [hcdsParams c ψ₁ ψ₂ hφ]
  have hchainsBelow : ∀ (ψ : Name → Nat) (c : Nat), c < q.k →
      ∀ chain ∈ chainsXBI (fun c' => uOf c' ψ)
        (fun c' => ((ppsOf c' ψ).drop q.nP).map (·.2.2))
        ((((ppsOf c ψ).drop q.nP).map (·.2.2)).length) (dZ.rss c) (dZ.tgtss c) (dZ.tlss c ψ)
        (dZ.Eiss c ψ) (dZ.Fss c ψ) (dZ.Ess c ψ), FieldsBelow (q.nP + 2) chain := by
    intro ψ c hc
    refine chainsXBI_below_of (n := (ctorsAs.getD c []).length) (fun c' => hIdsBelow c' ψ)
      (hlenFssZ c ψ)
      ?_ ?_ ?_ ?_ ?_
    · intro j hj i
      obtain ⟨cA, hjA⟩ : ∃ cA, (ctorsAs.getD c [])[j]? = some cA :=
        ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hTlssZD c j cA ψ hjA]
      exact (hpk₀ c hc j cA hjA).tssBelow ψ i
    · intro j hj i E hE
      obtain ⟨cA, hjA⟩ : ∃ cA, (ctorsAs.getD c [])[j]? = some cA :=
        ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hEissZD c j cA ψ hjA] at hE
      rw [hTlssZD c j cA ψ hjA]
      exact (hpk₀ c hc j cA hjA).eissBelow ψ i E hE
    · intro j hj
      obtain ⟨cA, hjA⟩ : ∃ cA, (ctorsAs.getD c [])[j]? = some cA :=
        ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hFssZD c j cA ψ hjA]
      have h := (DomsBelow.drop q.nP ((hpk₀ c hc j cA hjA).below ψ)).fields
      rwa [Nat.zero_add] at h
    · intro j hj
      obtain ⟨cA, hjA⟩ : ∃ cA, (ctorsAs.getD c [])[j]? = some cA :=
        ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hEssZD c j cA ψ hjA, hIdsLen c ψ]
      exact (hpk₀ c hc j cA hjA).lenE ψ
    · intro j hj E hE
      obtain ⟨cA, hjA⟩ : ∃ cA, (ctorsAs.getD c [])[j]? = some cA :=
        ⟨_, List.getElem?_eq_getElem hj⟩
      rw [hEssZD c j cA ψ hjA] at hE
      rw [hlenFsZ c j cA ψ hc hjA]
      exact (hpk₀ c hc j cA hjA).belowE ψ E hE
  -- ## a unit-like member's leaf folds to the one tagged empty tuple
  have hfoldZ : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      (ConLeche.blockCapsAt q j isRec).unitlike = true →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
        SpineFit ρ ((ppsOf j ψ).map (·.2.2)) ts →
        ts.foldl SetTheory.app (interp V ρ
            (blockTyAV q.k (q.resSort.eval ψ) (fun c => uOf c ψ)
              (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) dZ.rss dZ.tgtss
              (fun c => dZ.tlss c ψ) (fun c => dZ.Eiss c ψ) (fun c => dZ.Fss c ψ)
              (fun c => dZ.Ess c ψ) (ppsOf j ψ) j))
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
    -- the readings at that member
    have hIds0 : ((ppsOf j ψ).drop q.nP).map (·.2.2) = [] := by
      refine List.length_eq_zero_iff.mp ?_
      rw [hIdsLen j ψ, hnIdx0]
    have hlenP : (ppsOf j ψ).length = q.nP := by
      have := hlenPpsOf j hjk ψ
      rwa [hnIdx0, Nat.add_zero] at this
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
    have hρp : Sat V (((ppsOf j ψ).take q.nP).map (·.2.2)).reverse (consList ts ρ) := by
      rw [List.take_of_length_le (Nat.le_of_eq hlenP)]
      simpa using sat_of_spineFit (Sat_nil V ρ) hsp
    refine blockFoldSingle (Fs := []) (k := q.k) (m := j) hjk hIds0 hEss0 hsp
      (hbundle ψ (consList ts ρ) j hjk hρp).1 ?_
    rw [hFss0, hEss0]
    exact chainsRealBI_zero hIds0
  -- ## the REAL pass: the k formers at the FIXPOINT leaves
  obtain ⟨mpR, hEclR, hFDR, hfindR, hagR⟩ :=
    blockRealPass (uOf := uOf) (rsss := dZ.rss) (tgtsss := dZ.tgtss)
      (tlsss := fun c ψ => dZ.tlss c ψ) (Eisss := fun c ψ => dZ.Eiss c ψ)
      (fssZ := fun ψ c => dZ.Fss c ψ) (Esss := fun c ψ => dZ.Ess c ψ)
      mp hInd hF hndM hE hetaNe hetaFresh hIdsLen hIdsBelow hchainsBelow hZparams
      (fun j hj ψ ρp hρp =>
        ⟨fun c hc => (hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
            (hρpOf ψ ρp j hj hρp c hc)).1,
          fun c hc => (hIdxOf c (hcvOf c hc).choose (hcvOf c hc).choose_spec ψ ρp
            (hρpOf ψ ρp j hj hρp c hc)).2⟩)
      (fun j hj ψ ρp hρp => (hbundle ψ ρp j hj hρp).1.hok)
      (fun j hj ψ ρp hρp => (hbundle ψ ρp j hj hρp).2)
      hfoldZ
  -- ## the constructors, read again at the REAL carrier
  obtain ⟨pk, hpk⟩ : ∃ pk : Nat → BlockMemberPick, ∀ m : Nat, m < q.k →
      ∀ (j : Nat) (cA : ConstantVal × Nat), (ctorsAs.getD m [])[j]? = some cA →
        BlockCtorDataI mpR.base2 env (q.memberNames.getD m .anonymous)
          (fun i => q.memberNames.getD
            ((ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).getD i 0) .anonymous)
          (fun i => q.nIdxs.getD
            ((ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).getD i 0) 0)
          q.lps cA.1 q.nP cA.2 (q.nIdxs.getD m 0) q.resSort q.isProp q.large
          ((pk m).idxF j) ((pk m).dsF j) ((pk m).esF j) ((pk m).srcsF j)
          (((kinds.getD m []).getD j []).map ConLeche.BlockFieldKind.toRec)
          ((pk m).fvsPF j) ((pk m).xFvsF j) ((pk m).xrestF j) ((pk m).eissF j)
          ((pk m).tssF j) :=
    ⟨fun m => (hpickOf mpR (fun j cvTb hj => (hfindR j cvTb hj).1) m).choose,
      fun m => (hpickOf mpR (fun j cvTb hj => (hfindR j cvTb hj).1) m).choose_spec⟩
  -- ## the two readings agree off the recursive fields
  have hag : ∀ n : Name, (env.find? n).isSome = true →
      mpR.base2.acval n = mpD.base2.acval n := by
    intro n hn
    have hne' : ∀ cvTb ∈ cvTas, n ≠ cvTb.name := by
      intro cvTb hcvTb hh
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hcvTb
      rw [hh, hF.freshOf j cvTb hj] at hn
      exact nomatch hn
    rw [hagR n hne', hagD n hne']
  have hident : ∀ (m : Nat), m < q.k → ∀ (j : Nat) (cA : ConstantVal × Nat),
      (ctorsAs.getD m [])[j]? = some cA →
      (∀ ψ, (pk m).esF j ψ = (pk₀ m).esF j ψ) ∧
      (∀ ψ, (pk m).eissF j ψ = (pk₀ m).eissF j ψ) ∧
      (∀ ψ, (pk m).tssF j ψ = (pk₀ m).tssF j ψ) ∧
      ∀ (ψ : Name → Nat) (i : Nat), i < cA.2 →
        ((((kinds.getD m []).getD j []).map ConLeche.BlockFieldKind.toRec).getD i .ordinary
          ≠ .recursive) →
        ((((kinds.getD m []).getD j []).map ConLeche.BlockFieldKind.toRec).getD i .ordinary
          ≠ .reflexive) →
        (((pk m).dsF j ψ).getD (q.nP + i) default).2.2
          = (((pk₀ m).dsF j ψ).getD (q.nP + i) default).2.2 := by
    intro m hm j cA hj
    obtain ⟨-, -, -, -, h5, h6, h7, h8⟩ :=
      blockCtorDataI_ident hag (hpk m hm j cA hj) (hpk₀ m hm j cA hj)
    exact ⟨h5, h6, h7, h8⟩
  -- ## the record: the REAL data, with the DUMMY readings surviving
  -- only in the leaves' field lists
  have hnilCtors : ∀ c : Nat, ¬ c < q.k → ctorsAs.getD c [] = [] :=
    fun c hc => getD_of_le [] (by rw [hlenCtorsAs]; omega)
  have hTlssEq : ∀ (c : Nat) (ψ : Name → Nat),
      (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).tlss c ψ = dZ.tlss c ψ := by
    intro c ψ
    by_cases hc : c < q.k
    · show tlssOfR _ = tlssOfR _
      refine tlssOfR_fixCtorDataList_congr (ctorsAs.getD c []) 0 fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ : ∃ cAi, (ctorsAs.getD c [])[i]? = some cAi :=
        ⟨_, List.getElem?_eq_getElem hi⟩
      exact (hident c hc i cAi hi').2.2.1 ψ
    · show tlssOfR (fixCtorDataList _ _ _ _ _ _ (ctorsAs.getD c []) 0)
        = tlssOfR (fixCtorDataList _ _ _ _ _ _ (ctorsAs.getD c []) 0)
      rw [hnilCtors c hc]
      rfl
  have hEissEq : ∀ (c : Nat) (ψ : Name → Nat),
      (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Eiss c ψ = dZ.Eiss c ψ := by
    intro c ψ
    by_cases hc : c < q.k
    · show eissOfR _ = eissOfR _
      refine eissOfR_fixCtorDataList_congr (ctorsAs.getD c []) 0 fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ : ∃ cAi, (ctorsAs.getD c [])[i]? = some cAi :=
        ⟨_, List.getElem?_eq_getElem hi⟩
      exact (hident c hc i cAi hi').2.1 ψ
    · show eissOfR (fixCtorDataList _ _ _ _ _ _ (ctorsAs.getD c []) 0)
        = eissOfR (fixCtorDataList _ _ _ _ _ _ (ctorsAs.getD c []) 0)
      rw [hnilCtors c hc]
      rfl
  have hEssEq : ∀ (c : Nat) (ψ : Name → Nat),
      (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Ess c ψ = dZ.Ess c ψ := by
    intro c ψ
    by_cases hc : c < q.k
    · show essOfR _ = essOfR _
      refine essOfR_fixCtorDataList_congr (ctorsAs.getD c []) 0 fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ : ∃ cAi, (ctorsAs.getD c [])[i]? = some cAi :=
        ⟨_, List.getElem?_eq_getElem hi⟩
      exact (hident c hc i cAi hi').1 ψ
    · show essOfR (fixCtorDataList _ _ _ _ _ _ (ctorsAs.getD c []) 0)
        = essOfR (fixCtorDataList _ _ _ _ _ _ (ctorsAs.getD c []) 0)
      rw [hnilCtors c hc]
      rfl
  have hleafEq : ∀ (j : Nat) (ψ : Name → Nat),
      blockLeafZ (blockDataOf V q env ctorsAs kinds pk uOf ppsOf) (fun ψ' c => dZ.Fss c ψ') j ψ
        = blockTyAV q.k (q.resSort.eval ψ) (fun c => uOf c ψ)
            (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) dZ.rss dZ.tgtss
            (fun c => dZ.tlss c ψ) (fun c => dZ.Eiss c ψ) (fun c => dZ.Fss c ψ)
            (fun c => dZ.Ess c ψ) (ppsOf j ψ) j := by
    intro j ψ
    show blockTyAV _ _ _ _ _ _ _ _ _ _ _ _ = _
    rw [show (fun c => (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).tlss c ψ)
          = (fun c => dZ.tlss c ψ) from funext fun c => hTlssEq c ψ,
      show (fun c => (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Eiss c ψ)
          = (fun c => dZ.Eiss c ψ) from funext fun c => hEissEq c ψ,
      show (fun c => (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Ess c ψ)
          = (fun c => dZ.Ess c ψ) from funext fun c => hEssEq c ψ]
    rfl
  -- the targets name members at EVERY position (off the block the
  -- kinds are empty and the target falls back on member 0)
  have hlenKk : kinds.length = q.k := by rw [hlenK, hlenCtorsAs]
  have htgtAll : ∀ c j i : Nat,
      (ConLeche.blockTgtsOf ((kinds.getD c []).getD j [])).getD i 0 < q.k := by
    intro c j i
    by_cases hc : c < q.k
    · exact htgtLtK c hc j i
    · rw [getD_of_le [] (show kinds.length ≤ c from by omega),
        getD_of_le [] (show ([] : List (List ConLeche.BlockFieldKind)).length ≤ j from by simp)]
      simp only [ConLeche.blockTgtsOf, List.map_nil, List.getD_nil]
      exact hne
  have hctorLt : ∀ (c j : Nat) (cA : ConstantVal × Nat),
      (ctorsAs.getD c [])[j]? = some cA → c < q.k := by
    intro c j cA hj
    by_cases hc : c < q.k
    · exact hc
    · rw [hnilCtors c hc] at hj; exact nomatch hj
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
  have hCR := hchainsAt mpR pk (fun j cvTb hj => (hfindR j cvTb hj).1) hFDR hleafOfR hpk
  have htgtssEqR : ∀ (m j : Nat), j < (ctorsAs.getD m []).length →
      ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).tgtss m).getD j []
        = ConLeche.blockTgtsOf ((kinds.getD m []).getD j []) := by
    intro m j hj
    show ((List.range (ctorsAs.getD m []).length).map fun j' =>
      (List.range (((kinds.getD m []).getD j' []).map ConLeche.BlockFieldKind.toRec).length).map
        fun i => (ConLeche.blockTgtsOf ((kinds.getD m []).getD j' [])).getD i 0).getD j [] = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    show (List.range (((kinds.getD m []).getD j []).map _).length).map _ = _
    rw [List.length_map,
      show ((kinds.getD m []).getD j []).length
        = (ConLeche.blockTgtsOf ((kinds.getD m []).getD j [])).length from by
          show _ = (List.map _ _).length; rw [List.length_map]]
    exact hrangeGetD _
  have hFssRD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (ctorsAs.getD m [])[j]? = some cA →
      ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Fss m ψ).getD j []
        = (((pk m).dsF j ψ).drop q.nP).map (·.2.2) :=
    fun _ _ _ _ hj => fssOfR_fixCtorDataList_getD hj
  have hEssRD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (ctorsAs.getD m [])[j]? = some cA →
      ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Ess m ψ).getD j [] = (pk m).esF j ψ :=
    fun _ _ _ _ hj => essOfR_fixCtorDataList_getD hj
  have hTlssRD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (ctorsAs.getD m [])[j]? = some cA →
      ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).tlss m ψ).getD j []
        = (pk m).tssF j ψ :=
    fun _ _ _ _ hj => tlssOfR_fixCtorDataList_getD hj
  have hEissRD : ∀ (m j : Nat) (cA : ConstantVal × Nat) (ψ : Name → Nat),
      (ctorsAs.getD m [])[j]? = some cA →
      ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Eiss m ψ).getD j []
        = (pk m).eissF j ψ :=
    fun _ _ _ _ hj => eissOfR_fixCtorDataList_getD hj
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
  -- ## the constructors' stage, assembled
  have hSC : BlockCtorsStage (V := V) μ F (blockDataOf V q env ctorsAs kinds pk uOf ppsOf)
      q.lps cvTas q isRec
      (blockLeafZ (blockDataOf V q env ctorsAs kinds pk uOf ppsOf) (fun ψ c => dZ.Fss c ψ))
      (fun ψ c => dZ.Fss c ψ) envI q.ctorNamesAt := by
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
        ctors := fun m cvTa hm hcv =>
          ⟨_, _, _, blockCtorRuns_of hCtors hF.nameOf m cvTa hm hcv⟩
        nodup := ?_
        out := ?_
        lpsT := fun m cvTa hm hcv => hF.lpsOf m cvTa hcv
        lpsA := ?_
        pshape := ?_
        ndBlock := ?_
        paramsOf := fun m hm ψ ρp hρ c hc => hρpOf ψ ρp m hm hρ c hc
        lenPps := ?_
        lenIds := fun m hm ψ => hIdsLen m ψ
        chainsOk := ?_
        lenZ := fun m hm ψ => hlenFssZ m ψ
        lenZj := fun m hm ψ j cA hj => hlenFsZ m j cA ψ hm hj
        chainFactsZ := ?_
        chainFacts := ?_
        ord := ?_
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
    · -- chainsOk
      intro m hm ψ ρp hρp
      rw [show (fun c => (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).tlss c ψ)
            = (fun c => dZ.tlss c ψ) from funext fun c => hTlssEq c ψ,
        show (fun c => (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Eiss c ψ)
            = (fun c => dZ.Eiss c ψ) from funext fun c => hEissEq c ψ,
        show (fun c => (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Ess c ψ)
            = (fun c => dZ.Ess c ψ) from funext fun c => hEssEq c ψ]
      exact (hbundle ψ ρp m hm hρp).1
    · -- chainFactsZ
      intro m hm j cA hj ψ ρp hρp
      rw [htgtssEqR m j (List.getElem?_eq_some_iff.mp hj).1, hTlssEq m ψ, hEissEq m ψ, hEssEq m ψ,
        hTlssZD m j cA ψ hj, hEissZD m j cA ψ hj, hEssZD m j cA ψ hj, hFssZD m j cA ψ hj]
      exact (hCD m hm j cA hj ψ ρp hρp).1
    · -- chainFacts
      intro m hm j cA hj ψ ρp hρp
      rw [htgtssEqR m j (List.getElem?_eq_some_iff.mp hj).1, hTlssRD m j cA ψ hj,
        hEissRD m j cA ψ hj, hEssRD m j cA ψ hj, hFssRD m j cA ψ hj]
      exact (hCR m hm j cA hj ψ ρp hρp).1
    · -- ord
      intro m hm j cA hj ψ i hi hnr
      have hlenDR := (hpk m hm j cA hj).len ψ
      have hlenDZ := (hpk₀ m hm j cA hj).len ψ
      rw [hFssRD m j cA ψ hj, hFssZD m j cA ψ hj, drop_map_getD hlenDR hi,
        drop_map_getD hlenDZ hi]
      exact (hident m hm j cA hj).2.2.2 ψ i hi
        (fun hk => hnr ⟨Nat.le_add_right _ _, Or.inl (by rwa [Nat.add_sub_cancel_left])⟩)
        (fun hk => hnr ⟨Nat.le_add_right _ _, Or.inr (by rwa [Nat.add_sub_cancel_left])⟩)
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
          (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Fss m ψ = [[]] := by
        intro ψ
        have hl1 : ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Fss m ψ).length
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
          blockLeafZ (blockDataOf V q env ctorsAs kinds pk uOf ppsOf)
            (fun ψ' c => dZ.Fss c ψ') m ψ)
        (fun hU _ => absurd hu (by rw [hU]; simp))
        (fun ψ => (hlenP ψ).symm) hleaf' hFD'.read hFD'.okTy ?_ ?_ ?_
      · -- the fold at the fieldless shape
        intro _ ψ ρ ts hsp
        rw [hleafEq m ψ]
        exact hfoldZ m cvTa hcv hu ψ ρ ts hsp
      · -- the one constructor's leaf
        intro _ ψ
        have hleafCraw : m'.acval cA.1.name ψ
            = sumMkAV (q.resSort.eval ψ) 0 ((pk m).dsF 0 ψ)
                ((((pk m).dsF 0 ψ).drop q.nP).map (·.2.2))
                (uChains ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Fss m ψ)) :=
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
  -- ## the constructors' stage invariant at the REAL carrier
  have hcoreR : BlockCtorsCore mpR.base2 (blockDataOf V q env ctorsAs kinds pk uOf ppsOf)
      q.lps cvTas q isRec
      (blockLeafZ (blockDataOf V q env ctorsAs kinds pk uOf ppsOf) (fun ψ c => dZ.Fss c ψ)) 0 := by
    refine ⟨fun c cvTb hc => ⟨(hfindR c cvTb hc).1, hresIm _ (hF.resolveOf c cvTb hc),
        fun ψ => by rw [(hfindR c cvTb hc).2 ψ, hleafEq c ψ], hFDR c cvTb hc⟩,
      hfamFree', fun c j cA hj => ?_, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
    have hck : c < q.k := hctorLt c j cA hj
    obtain ⟨cvTa, hcv⟩ := hcvOf c hck
    obtain ⟨-, -, -, -, -, -, -, hres, -⟩ := (hfacts c cvTa hck hcv).2 j cA hj
    have hD := hpk c hck j cA hj
    refine ⟨hres, fun e he => ?_, hD⟩
    refine hresIm e ?_
    have he' : e ∈ (pk c).idxF j := he
    rw [hD.idxEq] at he'
    exact hD.opened.residRes e he'
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
  -- ## the k formers' leaves read the same at every frame (they are closed)
  have hAtR : ∀ c : Nat, c < q.k → ∀ (ψ : Name → Nat) (ρp σ : Nat → V),
      interp V σ (mpR.base2.acval
          ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).memberName c) ψ)
        = interp V (fun j => ρp (j + q.nP))
            (blockLeafZ (blockDataOf V q env ctorsAs kinds pk uOf ppsOf)
              (fun ψ' c' => dZ.Fss c' ψ') c ψ) := by
    intro c hc ψ ρp σ
    obtain ⟨cvTb, hcvTb⟩ := hcvOf c hc
    obtain ⟨-, -, hleaf, -⟩ := hcoreR.1 c cvTb hcvTb
    have hcl : ConLeche.Term.Term.bvarsBelow 0
        (blockLeafZ (blockDataOf V q env ctorsAs kinds pk uOf ppsOf)
          (fun ψ' c' => dZ.Fss c' ψ') c ψ).erase := by
      have := mpR.base2.cval_closedL cvTb.name ψ
      rwa [hleaf ψ] at this
    rw [show (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).memberName c = cvTb.name from
      (hF.nameOf c cvTb hcvTb).symm, hleaf ψ]
    exact interp_closed V hcl σ _
  -- ## a structure-like member's leaf folds to its one constructor's fibre
  have hfoldT : ∀ (m : Nat) (cA : ConstantVal × Nat), m < q.k → ctorsAs.getD m [] = [cA] →
      q.nIdxs.getD m 0 = 0 →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
        SpineFit ρ ((ppsOf m ψ).map (·.2.2)) ts →
        ts.foldl SetTheory.app (interp V ρ
            (blockLeafZ (blockDataOf V q env ctorsAs kinds pk uOf ppsOf)
              (fun ψ' c' => dZ.Fss c' ψ') m ψ))
          = sumSet (q.resSort.eval ψ) (sumFibre (q.resSort.eval ψ) (consList ts ρ)
              [((((pk m).dsF 0 ψ).drop q.nP).map (·.2.2)) ++ [idxEqAV []]]) := by
    intro m cA hm hcs hnIdx0 ψ ρ ts hsp
    have hcA : (ctorsAs.getD m [])[0]? = some cA := by rw [hcs]; rfl
    have hlenA : (ctorsAs.getD m []).length = 1 := by rw [hcs]; rfl
    have hIds0 : ((ppsOf m ψ).drop q.nP).map (·.2.2) = [] := by
      refine List.length_eq_zero_iff.mp ?_
      rw [hIdsLen m ψ, hnIdx0]
    have hlenP : (ppsOf m ψ).length = q.nP := by
      have := hlenPpsOf m hm ψ
      rwa [hnIdx0, Nat.add_zero] at this
    have hEss0 : (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Ess m ψ = [[]] := by
      obtain ⟨Es, hEs⟩ := List.length_eq_one_iff.mp (by
        show (essOfR _).length = 1
        rw [essOfR_length]
        exact (fixCtorDataList_length _ _ _ _ _ _ _ _).trans hlenA :
          ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Ess m ψ).length = 1)
      have hE0 : Es = (pk m).esF 0 ψ := by
        have h := hEssRD m 0 cA ψ hcA
        rwa [hEs] at h
      have hlen0 : ((pk m).esF 0 ψ).length = 0 := by
        have h := (hpk m hm 0 cA hcA).lenE ψ
        rwa [hnIdx0] at h
      rw [hEs, hE0, List.length_eq_zero_iff.mp hlen0]
    have hFss1 : (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Fss m ψ
        = [((((pk m).dsF 0 ψ).drop q.nP).map (·.2.2))] := by
      obtain ⟨Fs, hFs⟩ := List.length_eq_one_iff.mp (by
        show (fssOfR _ _).length = 1
        rw [fssOfR_length]
        exact (fixCtorDataList_length _ _ _ _ _ _ _ _).trans hlenA :
          ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).Fss m ψ).length = 1)
      have h0 := hFssRD m 0 cA ψ hcA
      rw [hFs] at h0 ⊢
      simp only [List.getD_cons_zero] at h0
      rw [h0]
    have hρp : Sat V (((ppsOf m ψ).take q.nP).map (·.2.2)).reverse (consList ts ρ) := by
      rw [List.take_of_length_le (Nat.le_of_eq hlenP)]
      simpa using sat_of_spineFit (Sat_nil V ρ) hsp
    refine blockFoldSingle (k := q.k) (m := m) hm hIds0 hEss0 hsp
      (hSC.chainsOk m hm ψ (consList ts ρ) hρp) ?_
    have hreal := blockChainsReal_of mpR.base2 (d := blockDataOf V q env ctorsAs kinds pk uOf ppsOf)
      (K := q.k) hm (fun j i => htgtAll m j i) (fun c hc ψ' ρp' σ => hAtR c hc ψ' ρp' σ)
      (fun j cB hj => (hcoreR.2.2.1 m j cB hj).2.2) (hSC.paramsOf m hm) hSC.lenPps
      (hSC.lenIds m hm) (hSC.chainsOk m hm) (hSC.lenZ m hm) (hSC.lenZj m hm)
      (hSC.chainFactsZ m hm) (hSC.chainFacts m hm) (hSC.ord m hm) ψ (consList ts ρ) hρp
    rwa [hFss1] at hreal
  refine ⟨pk, uOf, ppsOf, fun ψ c => dZ.Fss c ψ, mpR, ?_, ?_, hcoreR, ?_, ?_⟩
  · -- BlockNamesOk
    exact ⟨fun c cvTb hc => (hF.nameOf c cvTb hc).symm,
      fun c j i => by rw [hF.lenCv]; exact htgtAll c j i,
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
      rw [show (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).memberName m = cvTa.name from
        (hF.nameOf m cvTa hcv).symm]
      exact hF.pshapeOf m cvTa hcv
    · -- resT
      intro m hm
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      rw [show (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).memberName m = cvTa.name from
        (hF.nameOf m cvTa hcv).symm]
      exact hF.nresOf m cvTa hcv
    · -- resR: a member's recursor name is reserved only if the member's is
      intro m hm
      obtain ⟨cvTa, hcv⟩ := hcvOf m hm
      rw [show (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).memberName m = cvTa.name from
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
      rw [show (blockDataOf V q env ctorsAs kinds pk uOf ppsOf).memberName m = cvTa.name from
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
          ((blockDataOf V q env ctorsAs kinds pk uOf ppsOf).memberName m) i cA.1.type :=
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
