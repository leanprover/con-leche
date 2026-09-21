module

public import ConLeche.Model.Inductives.BlockAssembly
public import ConLeche.Model.Inductives.BlockStageTables
import ConLeche.Model.Inductives.BlockModel
import ConLeche.Model.Inductives.BlockCaps
import ConLeche.Semantics.Inductives.DeclBlock
import ConLeche.Verify.Inductives.BlockWF
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

/-- **A member's fixpoint leaf**, over the record's own chains. -/
@[expose] noncomputable def blockLeafAt (d : BlockData V) (c : Nat) (ψ : Name → Nat) :
    AnnotTerm :=
  blockTyAV d.k (d.w ψ) (fun c' => d.uM c' ψ) (fun c' => d.IdsM c' ψ) d.rss d.tgtss
    (fun c' => d.tlss c' ψ) (fun c' => d.Eiss c' ψ) (fun c' => d.Fss c' ψ)
    (fun c' => d.Ess c' ψ) (d.ppsM c ψ) c

/-! ## A name absent after the formers' conses is absent before them -/

/-- The `k` formers' conses add names; they take none away. -/
theorem consBlockInds_find?_none {p₁ : BlockShape} {isRec : Bool} :
    ∀ {cvTas : List ConstantVal} {i : Nat} {env : Env} {n : Name},
      (ConLeche.consBlockInds p₁ isRec cvTas i env).find? n = none → env.find? n = none
  | [], _, _, _, h => h
  | _ :: _, _, _, _, h => find?_none_of_consB (consBlockInds_find?_none h)

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

/-- **One member's constructors, as stored**: `declNative`'s `hrunOf`
at a block member. -/
theorem blockCtorFacts_of {envI : Env} {q : BlockShape} {F : Nat} {cvTa : ConstantVal} {m : Nat}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hrun : ConLeche.checkSumCtors (ConLeche.fueledOps μ F) envI envI cvTa.name q.lps q.nP
        (q.nIdxs.getD m 0) q.resSort q.isProp q.large cvTa (q.members.getD m default).ctors
      = .ok (ctorsA, sortss))
    (hClps : ∀ c ∈ (q.members.getD m default).ctors, c.1.levelParams = q.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false) :
    ctorsA.length = (q.members.getD m default).ctors.length ∧
    ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ (c : ConstantVal × Nat) (sorts : List Level),
        (q.members.getD m default).ctors[j]? = some c ∧
        cA.1.name = c.1.name ∧ cA.2 = c.2 ∧ cA.1.levelParams = q.lps ∧
        envI.find? cA.1.name = none ∧ cA.1.type.constsResolve envI = true ∧
        cA.1.name.isProjFnShape = false ∧
        ConLeche.reservedBasisNames.contains cA.1.name = false ∧
        sortss[j]? = some sorts ∧
        ConLeche.checkSumCtor (ConLeche.fueledOps μ F) envI envI cvTa.name q.lps q.nP
          (q.nIdxs.getD m 0) q.resSort q.isProp q.large c.1 cA.2 cvTa = .ok (cA.1, sorts) := by
  obtain ⟨hlenA, -, hall⟩ := ConLeche.checkSumCtors_inv hrun
  refine ⟨hlenA, fun j cA hj => ?_⟩
  have hjl : j < (q.members.getD m default).ctors.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1; omega
  obtain ⟨hnF, sorts, hsj, hCtor⟩ :=
    hall j ((q.members.getD m default).ctors[j]) cA (List.getElem?_eq_getElem hjl) hj
  obtain ⟨⟨_, hccvC⟩, -, -⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨hfindC, -, hpshapeC, -, -, -, _, -, -, -, -, htrC, -, -, htyC⟩ :=
    ConLeche.checkConstantVal_inv hccvC
  have hmem : (q.members.getD m default).ctors[j] ∈ (q.members.getD m default).ctors :=
    List.getElem_mem hjl
  refine ⟨_, sorts, List.getElem?_eq_getElem hjl, by rw [htyC], hnF, ?_, ?_, ?_,
    by rw [htyC]; exact hpshapeC, ?_, hsj, by rw [hnF]; exact hCtor⟩
  · rw [htyC]; exact (hClps _ hmem).1
  · show Env.find? _ cA.1.name = none
    rw [htyC]; exact hfindC
  · show Expr.constsResolve _ cA.1.type = true
    rw [htyC]; exact htrC
  · rw [htyC]; exact (hClps _ hmem).2

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
      obtain ⟨hlenA, hfacts⟩ := blockCtorFacts_of hrun (fun c' hc' => hClps c' (by
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

/-- **Every target a constructor's kinds carry names a member** (the
`blockTgtsOf` reading of `blockCtorKinds_tgt_lt`). -/
theorem blockTgtsOf_lt {names lps : List Name} {nP : Nat} {nIdxs : List Nat}
    (hne : names ≠ []) {c : ConstantVal × Nat} {ks : List ConLeche.BlockFieldKind}
    (h : ConLeche.blockCtorKinds names lps nP nIdxs c = some ks) (i : Nat) :
    (ConLeche.blockTgtsOf ks).getD i 0 < names.length := by
  have hpos : 0 < names.length := by
    cases names with
    | nil => exact absurd rfl hne
    | cons a l => simp
  show ((ks.map _).getD i 0) < names.length
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hk : ks[i]? with
  | none => simpa using hpos
  | some kk =>
    have hmem : kk ∈ ks := List.mem_of_getElem? hk
    cases kk with
    | ordinary => simpa using hpos
    | negative => simpa using hpos
    | unsupported => simpa using hpos
    | recursive t =>
      show t < names.length
      exact ConLeche.blockCtorKinds_tgt_lt hne h (Or.inl hmem)
    | reflexive t =>
      show t < names.length
      exact ConLeche.blockCtorKinds_tgt_lt hne h (Or.inr hmem)

end ConLeche.Model
