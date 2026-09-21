module

public import ConLeche.Model.Inductives.BlockCtorsLoop
public import ConLeche.Model.Inductives.BlockCaps
public import ConLeche.Model.Inductives.BlockRealChains
public import ConLeche.Model.Inductives.BlockRep
import ConLeche.Semantics.Inductives.DeclSumEta
public section

/-!
# The constructors' stage at a block member (task #315 M3)

`BlockCtorsCore`: what the `k` constructor loops thread — the `k`
formers found with their leaves and their telescope readings, the
capability families still free, every member's constructors' data at
the carrier, and the constructors consed SO FAR with their leaves.
It is `declNative`'s `Inv` at `k` members, and it is exactly what a
constructor cons preserves (`BlockCtorsCore.cons`).

`stageBlockCtorsAt` is `declNative`'s member-local half at member `m`:
the fibre law of the member's own fixpoint leaf (`blockFold_of` over
the member's REAL chains, built here from the block's operator premise
and the dummy/real identification), the member's capability laws
(`blockCapsLawsAt`), and then `blockCtorsLoop` — so the stage's output
is the carrier after `consSumCtors` of that member's constructors,
with the core invariant one member further on.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  InductiveShape BlockShape BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The invariant the member loops thread -/

/-- **The block install's carrier invariant at the constructors'
stage**, `nc` members' constructors consed: the `k` formers with their
leaves and telescope readings, the capability families free, every
member's constructors' readings, the earlier members' constructors
stored with their leaves. -/
@[expose] def BlockCtorsCore {env : Env} (m' : EnvModel V env) (d : BlockData V)
    (lps : List Name) (cvTasAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm) (nc : Nat) : Prop :=
  -- the `k` formers
  (∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      cvTb.type.constsResolve env = true ∧
      (∀ ψ, m'.acval cvTb.name ψ = A c ψ) ∧
      FormerData m' cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)) ∧
  -- a capable member's projection-function family is still free
  (∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      (ConLeche.blockCapsAt p₁ c isRec).unitlike = false →
      (ConLeche.blockCapsAt p₁ c isRec).eta = true →
      env.find? (projFnName cvTb.name 0) = none) ∧
  -- every member's constructors resolve and read
  (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.type.constsResolve env = true ∧
      (∀ e ∈ d.idxF c j, e.constsResolve env = true) ∧
      BlockCtorDataI m' d.env₀ (d.memberName c) (fun i => d.memberName (d.tgts c j i))
        (fun i => d.nIdxAt (d.tgts c j i)) lps cA.1 d.nP cA.2 (d.nIdxAt c) d.resSort d.isProp
        d.large (d.idxF c j) (d.dsF c j) (d.esF c j) (d.srcsF c j) (d.ksF c j) (d.fvsPF c j)
        (d.xFvsF c j) (d.xrestF c j) (d.eissF c j) (d.tssF c j)) ∧
  -- the members before `nc`: their constructors are stored with their leaves
  (∀ c, c < nc → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      env.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2) ∧ cA.1.levelParams = lps ∧
      ∀ ψ, m'.acval cA.1.name ψ
        = sumMkAV (d.w ψ) j (d.dsF c j ψ) (((d.dsF c j ψ).drop d.nP).map (·.2.2))
            (uChains (d.Fss c ψ)))

/-- **The block's names, statically**: a member's name is its former's,
and every field's target is a member. -/
@[expose] def BlockNamesOk (d : BlockData V) (cvTasAll : List ConstantVal) : Prop :=
  (∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb → d.memberName c = cvTb.name) ∧
  (∀ c j i : Nat, d.tgts c j i < cvTasAll.length) ∧
  ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA → c < cvTasAll.length

/-- **The core invariant survives a constructor's cons.**  A stored
name is not the fresh one, so nothing found before is disturbed; the
readings cross by `FormerData.cross` and `BlockCtorDataI.cross`. -/
theorem BlockCtorsCore.cons {env : Env} {m' : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hN : BlockNamesOk (V := V) d cvTasAll)
    (h : BlockCtorsCore m' d lps cvTasAll p₁ isRec A nc)
    {cA : ConstantVal × Nat} {B : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? cA.1.name = none)
    (hpshape : cA.1.name.isProjFnShape = false)
    (mC : EnvModel V ⟨.ctorInfo cA.1 d.nP cA.2 :: env.consts⟩)
    (hac : mC.acval = acvalWith m'.acval cA.1.name B) :
    BlockCtorsCore mC d lps cvTasAll p₁ isRec A nc := by
  obtain ⟨hnameOf, htgtLt, hctorLt⟩ := hN
  obtain ⟨hform, hfr, hdata, hconsed⟩ := h
  have hcross : ∀ e : Expr, ConsCrossAt (.ctorInfo cA.1 d.nP cA.2) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ hh => nomatch hh)
  -- a name already stored is not the fresh one
  have hne : ∀ n : Name, (env.find? n).isSome = true → n ≠ cA.1.name := by
    intro n hn hnn
    rw [hnn, hfresh] at hn
    exact nomatch hn
  have hneOf : ∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      cvTb.name ≠ cA.1.name := by
    intro c cvTb hc
    exact hne _ (by rw [(hform c cvTb hc).1]; rfl)
  refine ⟨fun c cvTb hc => ?_, fun c cvTb hc hU he => ?_, fun c j cB hj => ?_,
    fun c hc j cB hj => ?_⟩
  · obtain ⟨hfind, hres, hleaf, hFD⟩ := hform c cvTb hc
    refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfind,
      Expr.constsResolve_mono hres, fun ψ => ?_, ?_⟩
    · rw [hac]
      show acvalWith m'.acval cA.1.name B cvTb.name ψ = _
      rw [acvalWith_ne (hneOf c cvTb hc)]
      exact hleaf ψ
    · exact hFD.cross (c₀ := .ctorInfo cA.1 d.nP cA.2) hfresh (hcross _)
        (constsBound_of_constsResolve _ hres) mC hac
  · have hnp : ¬ ((ConstantInfo.ctorInfo cA.1 d.nP cA.2).name = projFnName cvTb.name 0) := by
      intro hh
      have hh' : cA.1.name = projFnName cvTb.name 0 := hh
      have := projFnName_isProjFnShape cvTb.name 0
      rw [← hh', hpshape] at this
      exact nomatch this
    rw [ConLeche.Env.find?_cons, if_neg hnp]
    exact hfr c cvTb hc hU he
  · obtain ⟨hres, hresI, hD⟩ := hdata c j cB hj
    refine ⟨Expr.constsResolve_mono hres, fun e he => Expr.constsResolve_mono (hresI e he), ?_⟩
    refine hD.cross (c₀ := .ctorInfo cA.1 d.nP cA.2) hfresh ?_ ?_ hcross
      (constsBound_of_constsResolve _ hres)
      (fun e he => constsBound_of_constsResolve _ (hresI e he)) mC hac
    · obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTasAll[c]? = some cvTb :=
        ⟨_, List.getElem?_eq_getElem (hctorLt c j cB hj)⟩
      rw [hnameOf c cvTb hcvTb]
      exact hneOf c cvTb hcvTb
    · intro i
      obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTasAll[d.tgts c j i]? = some cvTb :=
        ⟨_, List.getElem?_eq_getElem (htgtLt c j i)⟩
      rw [hnameOf _ cvTb hcvTb]
      exact hneOf _ cvTb hcvTb
  · obtain ⟨hfind, hlps, hleaf⟩ := hconsed c hc j cB hj
    refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfind, hlps, fun ψ => ?_⟩
    rw [hac]
    show acvalWith m'.acval cA.1.name B cB.1.name ψ = _
    rw [acvalWith_ne (hne _ (by rw [hfind]; rfl))]
    exact hleaf ψ

/-! ## The member's real chains -/

set_option maxHeartbeats 1600000 in
/-- **A block member's REAL chains against the LEAF's**
(`declNative`'s `hreal` at `k` members): constructor by constructor,
`blockChainReal_of` from the block operator's premise at the leaf's
chains (`hX`), the per-constructor chain facts at both the leaf's
chains and the real ones, and their identification off the recursive
fields (`hord`).  The recursive entries are the TARGET member's leaf,
read by `hAt` at any frame. -/
theorem blockChainsReal_of {env' : Env} (m' : EnvModel V env') {d : BlockData V}
    {lps : List Name} {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {K m : Nat}
    (hm : m < d.k)
    (htgtLt : ∀ j i : Nat, d.tgts m j i < K)
    (hAt : ∀ c : Nat, c < K → ∀ (ψ : Name → Nat) (ρp σ : Nat → V),
      interp V σ (m'.acval (d.memberName c) ψ)
        = interp V (fun j => ρp (j + d.nP))
            (blockTyAV d.k (d.w ψ) (fun c' => d.uM c' ψ) (fun c' => d.IdsM c' ψ) d.rss d.tgtss
              (fun c' => d.tlss c' ψ) (fun c' => d.Eiss c' ψ) (fssZ ψ) (fun c' => d.Ess c' ψ)
              (d.ppsM c ψ) c))
    (hdata : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      BlockCtorDataI m' d.env₀ (d.memberName m) (fun i => d.memberName (d.tgts m j i))
        (fun i => d.nIdxAt (d.tgts m j i)) lps cA.1 d.nP cA.2 (d.nIdxAt m) d.resSort d.isProp
        d.large (d.idxF m j) (d.dsF m j) (d.esF m j) (d.srcsF m j) (d.ksF m j) (d.fvsPF m j)
        (d.xFvsF m j) (d.xrestF m j) (d.eissF m j) (d.tssF m j))
    (hρpOf : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
      ∀ c, c < d.k → Sat V (((d.ppsM c ψ).take d.nP).map (·.2.2)).reverse ρp)
    (hlenPps : ∀ (c : Nat) (ψ : Name → Nat), c < d.k →
      (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length)
    (hlenIds : ∀ ψ : Name → Nat, (d.IdsM m ψ).length = d.nIdxAt m)
    (hX : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
      BlockChainsOk d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) d.rss d.tgtss
        (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fssZ ψ) (fun c => d.Ess c ψ))
    (hlenZ : ∀ ψ : Name → Nat, (fssZ ψ m).length = (d.ctorsM m).length)
    (hlenZj : ∀ (ψ : Name → Nat) (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[j]? = some cA → ((fssZ ψ m).getD j []).length = cA.2)
    (hC₀ : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
      ChainFactsB d.k (d.w ψ) d.nP cA.2 ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) m
        (d.ksF m j) ((d.tgtss m).getD j []) ((d.tlss m ψ).getD j []) ((fssZ ψ m).getD j [])
        ((d.Eiss m ψ).getD j []) ((d.Ess m ψ).getD j []))
    (hC : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
      ChainFactsB d.k (d.w ψ) d.nP cA.2 ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) m
        (d.ksF m j) ((d.tgtss m).getD j []) ((d.tlss m ψ).getD j []) ((d.Fss m ψ).getD j [])
        ((d.Eiss m ψ).getD j []) ((d.Ess m ψ).getD j []))
    (hord : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      ∀ (ψ : Name → Nat) (i : Nat), i < cA.2 → ¬ recAt d.nP (d.ksF m j) (d.nP + i) →
      ((d.Fss m ψ).getD j []).getD i default = ((fssZ ψ m).getD j []).getD i default) :
    ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
      ChainsRealBI (blockFam d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) d.rss
          d.tgtss (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fssZ ψ) (fun c => d.Ess c ψ))
        d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) m (d.rss m) (d.tgtss m)
        (d.tlss m ψ) (d.Eiss m ψ) (fssZ ψ m) (d.Fss m ψ) (d.Ess m ψ) := by
  have hdata : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      True ∧ True ∧ (c = m → BlockCtorDataI m' d.env₀ (d.memberName c)
        (fun i => d.memberName (d.tgts c j i)) (fun i => d.nIdxAt (d.tgts c j i)) lps cA.1 d.nP
        cA.2 (d.nIdxAt c) d.resSort d.isProp d.large (d.idxF c j) (d.dsF c j) (d.esF c j)
        (d.srcsF c j) (d.ksF c j) (d.fvsPF c j) (d.xFvsF c j) (d.xrestF c j) (d.eissF c j)
        (d.tssF c j)) :=
    fun c j cA hj => ⟨trivial, trivial, fun hc => by subst hc; exact hdata j cA hj⟩

  -- ## the member's data, by position
  have hlenFss : ∀ ψ : Name → Nat, (d.Fss m ψ).length = (d.ctorsM m).length := by
    intro ψ
    show (fssOfR _ _).length = _
    rw [fssOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hlenEss : ∀ ψ : Name → Nat, (d.Ess m ψ).length = (d.ctorsM m).length := by
    intro ψ
    show (essOfR _).length = _
    rw [essOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hFssD : ∀ (ψ : Name → Nat) (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[j]? = some cA →
      (d.Fss m ψ).getD j [] = ((d.dsF m j ψ).drop d.nP).map (·.2.2) :=
    fun ψ j cA hj => fssOfR_fixCtorDataList_getD hj
  have hEssD : ∀ (ψ : Name → Nat) (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[j]? = some cA → (d.Ess m ψ).getD j [] = d.esF m j ψ :=
    fun ψ j cA hj => essOfR_fixCtorDataList_getD hj
  have hTlssD : ∀ (ψ : Name → Nat) (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[j]? = some cA → (d.tlss m ψ).getD j [] = d.tssF m j ψ :=
    fun ψ j cA hj => tlssOfR_fixCtorDataList_getD hj
  have hEissD : ∀ (ψ : Name → Nat) (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[j]? = some cA → (d.Eiss m ψ).getD j [] = d.eissF m j ψ :=
    fun ψ j cA hj => eissOfR_fixCtorDataList_getD hj
  have hFssEq : ∀ ψ : Name → Nat,
      d.Fss m ψ = fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0) :=
    fun ψ => fssOfR_fixCtorDataList _ _ _ _ _ _ _ _ _
  have hrssD : ∀ (j : Nat), j < (d.ctorsM m).length → (d.rss m).getD j [] = rsOf (d.ksF m j) :=
    fun j hj => rssOfK_getD hj
  have hksLen : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      (d.ksF m j).length = cA.2 := fun j cA hj => ((hdata m j cA hj).2.2 rfl).ksLen
  have htgtsD : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      ∀ i, i < cA.2 → ((d.tgtss m).getD j []).getD i 0 = d.tgts m j i := by
    intro j cA hj i hi
    have hjl : j < (d.ctorsM m).length := (List.getElem?_eq_some_iff.mp hj).1
    have hil : i < (d.ksF m j).length := by rw [hksLen j cA hj]; exact hi
    have h1 : (d.tgtss m).getD j [] = (List.range (d.ksF m j).length).map (d.tgts m j) := by
      show (((List.range (d.ctorsM m).length).map fun j' =>
        (List.range (d.ksF m j').length).map (d.tgts m j')).getD j []) = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hjl]
      rfl
    rw [h1, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hil]
    rfl
  -- ## the member's REAL chains against the leaf's
  intro ψ ρp hρp
  refine ⟨by rw [hlenZ, hlenFss], by rw [hlenEss, hlenFss], fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_⟩
  · rw [hlenFss] at hj
    obtain ⟨cA, hjA⟩ : ∃ cA, (d.ctorsM m)[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
    rw [hEssD ψ j cA hjA, hlenIds]
    exact ((hdata m j cA hjA).2.2 rfl).lenE ψ
  · rw [hlenFss] at hj
    obtain ⟨cA, hjA⟩ : ∃ cA, (d.ctorsM m)[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
    rw [hlenZj ψ j cA hjA, hFssD ψ j cA hjA]
    simp [((hdata m j cA hjA).2.2 rfl).len ψ]
  · rw [hlenFss] at hj
    obtain ⟨cA, hjA⟩ : ∃ cA, (d.ctorsM m)[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
    have hD := ((hdata m j cA hjA).2.2 rfl)
    have hlenD := hD.len ψ
    have hCj := hC j cA hjA ψ ρp hρp
    have hC₀j := hC₀ j cA hjA ψ ρp hρp
    rw [hrssD j hj]
    refine blockChainReal_of (ppsOf := fun c => d.ppsM c ψ)
      (AOf := fun i => m'.acval (d.memberName (d.tgts m j i)) ψ)
      (hX ψ ρp hρp).hI (hX ψ ρp hρp).hok hC₀j
      (fun c hc => hlenPps c ψ hc) (fun _ _ => rfl) (fun c hc => hρpOf ψ ρp hρp c hc)
      ?_ ?_ (fun i hi => hCj.nb i hi) (fun i hi hnr => hord j cA hjA ψ i hi hnr) ?_ ?_
      (fun i hnr => by rw [hTlssD ψ j cA hjA]; exact hD.tssNone ψ i hnr)
      (fun i dd hdd => by
        rw [hTlssD ψ j cA hjA] at hdd
        exact hD.tssBits ψ i dd hdd)
    · -- the target member's leaf, at any frame
      intro i hi hr σ
      rw [htgtsD j cA hjA i hi]
      exact hAt (d.tgts m j i) (htgtLt j i) ψ ρp σ
    · rw [hFssD ψ j cA hjA]
      simp [hlenD]
    · -- a finitary field's entry
      intro i hi hk
      rw [hFssD ψ j cA hjA]
      rw [drop_map_getD hlenD hi, hD.recEntry ψ i hk hi, hEissD ψ j cA hjA]
    · -- a reflexive field's entry
      intro i hi hk
      rw [hFssD ψ j cA hjA]
      rw [drop_map_getD hlenD hi, hD.reflEntry ψ i hk hi, hEissD ψ j cA hjA,
        hTlssD ψ j cA hjA]

/-! ## The stage at one member -/

set_option maxHeartbeats 1600000 in
/-- **The constructors' stage at one block member**: `declNative`'s
member-local half at member `m`.  The member's own fibre law
(`blockFold_of` over the member's REAL chains, assembled here from the
block operator's premise at the LEAF's chains and the dummy/real
identification at the ordinary fields) and its capability laws feed
`blockCtorsLoop`; the carrier that comes out is the one after that
member's `consSumCtors`, with the core invariant one member on. -/
theorem stageBlockCtorsAt (hμ : μ.verifiedChecks = true) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)}
    {envI env : Env} {ctorsOf : Name → List Name} {ctors : List (ConstantVal × Nat)}
    {sortss : List (List Level)} {m : Nat} {cvTa : ConstantVal}
    (hN : BlockNamesOk (V := V) d cvTasAll)
    (hm : m < d.k) (hcvTa : cvTasAll[m]? = some cvTa)
    -- the leaves the `k` formers were consed with
    (hA : ∀ (c : Nat) (ψ : Name → Nat), A c ψ
      = blockTyAV d.k (d.w ψ) (fun c' => d.uM c' ψ) (fun c' => d.IdsM c' ψ) d.rss d.tgtss
          (fun c' => d.tlss c' ψ) (fun c' => d.Eiss c' ψ) (fssZ ψ) (fun c' => d.Ess c' ψ)
          (d.ppsM c ψ) c)
    -- the member's constructors, as checked
    (hCtors : ConLeche.checkSumCtors (ConLeche.fueledOps μ F) envI envI cvTa.name lps d.nP
      (d.nIdxAt m) d.resSort d.isProp d.large cvTa ctors = .ok (d.ctorsM m, sortss))
    (hnd : ((d.ctorsM m).map (·.1.name)).Nodup)
    (hout : ∀ cA ∈ d.ctorsM m, ∀ T'' ∈ d.memberNames, T'' ≠ cvTa.name → cA.1.name ∉ ctorsOf T'')
    (hlpsT : cvTa.levelParams = lps)
    (hlpsA : ∀ cA ∈ d.ctorsM m, cA.1.levelParams = lps)
    (hpshapeA : ∀ cA ∈ d.ctorsM m, cA.1.name.isProjFnShape = false)
    (hndBlock : ∀ (c : Nat), c ≠ m → ∀ (j : Nat) (cB : ConstantVal × Nat),
      (d.ctorsM c)[j]? = some cB → cB.1.name ∉ (d.ctorsM m).map (·.1.name))
    -- the members' parameter telescopes, interchangeable (official's agreement)
    (hρpOf : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
      ∀ c, c < d.k → Sat V (((d.ppsM c ψ).take d.nP).map (·.2.2)).reverse ρp)
    (hlenPps : ∀ (c : Nat) (ψ : Name → Nat), c < d.k →
      (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length)
    (hlenIds : ∀ ψ : Name → Nat, (d.IdsM m ψ).length = d.nIdxAt m)
    -- the block operator's premise, at the LEAF's chains
    (hX : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
      BlockChainsOk d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) d.rss d.tgtss
        (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fssZ ψ) (fun c => d.Ess c ψ))
    -- the member's chain facts, at the leaf's chains and at the real ones
    (hlenZ : ∀ ψ : Name → Nat, (fssZ ψ m).length = (d.ctorsM m).length)
    (hlenZj : ∀ (ψ : Name → Nat) (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[j]? = some cA → ((fssZ ψ m).getD j []).length = cA.2)
    (hC₀ : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
      ChainFactsB d.k (d.w ψ) d.nP cA.2 ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) m
        (d.ksF m j) ((d.tgtss m).getD j []) ((d.tlss m ψ).getD j []) ((fssZ ψ m).getD j [])
        ((d.Eiss m ψ).getD j []) ((d.Ess m ψ).getD j []))
    (hC : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
      ChainFactsB d.k (d.w ψ) d.nP cA.2 ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) m
        (d.ksF m j) ((d.tgtss m).getD j []) ((d.tlss m ψ).getD j []) ((d.Fss m ψ).getD j [])
        ((d.Eiss m ψ).getD j []) ((d.Ess m ψ).getD j []))
    -- the leaf's chains and the real ones agree off the recursive fields
    (hord : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      ∀ (ψ : Name → Nat) (i : Nat), i < cA.2 → ¬ recAt d.nP (d.ksF m j) (d.nP + i) →
      ((d.Fss m ψ).getD j []).getD i default = ((fssZ ψ m).getD j []).getD i default)
    -- the constructors' frames at the member's parameter telescope
    (hframes : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρ ↔
          Sat V (((d.dsF m j ψ).take d.nP).map (·.2.2)).reverse ρ) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((d.dsF m j ψ).take d.nP).map (·.2.2)).reverse ρ →
          FieldsOkB (d.w ψ) ρ (((d.dsF m j ψ).drop d.nP).map (·.2.2)) ∧
          FieldsValid ρ (((d.dsF m j ψ).drop d.nP).map (·.2.2)) ∧
          (∀ bs : List V, SpineFit ρ (((d.dsF m j ψ).drop d.nP).map (·.2.2)) bs →
            SpineFit ρ (d.IdsM m ψ) (idxValsAt ρ (d.esF m j ψ) bs))))
    -- the unit-like arm's capability laws (`blockCapsLawsAtUnit`)
    (hcapsU : ∀ {env' : Env} (m' : EnvModel V env') (kk : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[kk]? = some cA →
      (ConLeche.blockCapsAt p₁ m isRec).unitlike = true →
      FormerData m' cvTa (d.nP + d.nIdxAt m) d.resSort (d.ppsM m) →
      (∀ ψ, m'.acval cvTa.name ψ = A m ψ) →
      (∀ ψ, m'.acval cA.1.name ψ = sumMkAV (d.w ψ) kk (d.dsF m kk ψ)
        (((d.dsF m kk ψ).drop d.nP).map (·.2.2)) (uChains (d.Fss m ψ))) →
      CapsLawsAt m' cvTa.name cvTa (ConLeche.blockCapsAt p₁ m isRec))
    (mp : EnvModelM V μ env)
    (hE : ConLeche.BlockEtaInv env d.memberNames ctorsOf)
    (hinv : BlockCtorsCore mp.base2 d lps cvTasAll p₁ isRec A m)
    (hfreshC : ∀ c, m ≤ c → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      env.find? cA.1.name = none) :
    ∃ mp' : EnvModelM V μ (ConLeche.consSumCtors d.nP (d.ctorsM m) env),
      ConLeche.BlockEtaInv (ConLeche.consSumCtors d.nP (d.ctorsM m) env) d.memberNames ctorsOf ∧
      BlockCtorsCore mp'.base2 d lps cvTasAll p₁ isRec A (m + 1) ∧
      ∀ c, m + 1 ≤ c → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
        (ConLeche.consSumCtors d.nP (d.ctorsM m) env).find? cA.1.name = none := by
  obtain ⟨hnameOf, htgtLt, hctorLt⟩ := hN
  obtain ⟨hform, hfrP, hdata, hconsed⟩ := hinv
  have hTname : d.memberName m = cvTa.name := hnameOf m cvTa hcvTa
  obtain ⟨hfindT, hresT, hleafT, hFD⟩ := hform m cvTa hcvTa
  -- ## the leaves read the same at every frame (they are closed)
  have hAt : ∀ c : Nat, c < cvTasAll.length → ∀ (ψ : Name → Nat) (ρp σ : Nat → V),
      interp V σ (mp.base2.acval (d.memberName c) ψ)
        = interp V (fun j => ρp (j + d.nP))
            (blockTyAV d.k (d.w ψ) (fun c' => d.uM c' ψ) (fun c' => d.IdsM c' ψ) d.rss d.tgtss
              (fun c' => d.tlss c' ψ) (fun c' => d.Eiss c' ψ) (fssZ ψ) (fun c' => d.Ess c' ψ)
              (d.ppsM c ψ) c) := by
    intro c hc ψ ρp σ
    obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTasAll[c]? = some cvTb := ⟨_, List.getElem?_eq_getElem hc⟩
    obtain ⟨-, -, hleaf, -⟩ := hform c cvTb hcvTb
    have hcl : Term.bvarsBelow 0 (A c ψ).erase := by
      have := mp.base2.cval_closedL cvTb.name ψ
      rwa [hleaf ψ] at this
    rw [hnameOf c cvTb hcvTb, hleaf ψ, ← hA c ψ]
    exact interp_closed V hcl σ _
  -- ## the member's data, by position
  have hlenFss : ∀ ψ : Name → Nat, (d.Fss m ψ).length = (d.ctorsM m).length := by
    intro ψ
    show (fssOfR _ _).length = _
    rw [fssOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hlenEss : ∀ ψ : Name → Nat, (d.Ess m ψ).length = (d.ctorsM m).length := by
    intro ψ
    show (essOfR _).length = _
    rw [essOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hFssD : ∀ (ψ : Name → Nat) (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[j]? = some cA →
      (d.Fss m ψ).getD j [] = ((d.dsF m j ψ).drop d.nP).map (·.2.2) :=
    fun ψ j cA hj => fssOfR_fixCtorDataList_getD hj
  have hEssD : ∀ (ψ : Name → Nat) (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[j]? = some cA → (d.Ess m ψ).getD j [] = d.esF m j ψ :=
    fun ψ j cA hj => essOfR_fixCtorDataList_getD hj
  have hTlssD : ∀ (ψ : Name → Nat) (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[j]? = some cA → (d.tlss m ψ).getD j [] = d.tssF m j ψ :=
    fun ψ j cA hj => tlssOfR_fixCtorDataList_getD hj
  have hEissD : ∀ (ψ : Name → Nat) (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[j]? = some cA → (d.Eiss m ψ).getD j [] = d.eissF m j ψ :=
    fun ψ j cA hj => eissOfR_fixCtorDataList_getD hj
  have hFssEq : ∀ ψ : Name → Nat,
      d.Fss m ψ = fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0) :=
    fun ψ => fssOfR_fixCtorDataList _ _ _ _ _ _ _ _ _
  have hrssD : ∀ (j : Nat), j < (d.ctorsM m).length → (d.rss m).getD j [] = rsOf (d.ksF m j) :=
    fun j hj => rssOfK_getD hj
  have hksLen : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      (d.ksF m j).length = cA.2 := fun j cA hj => (hdata m j cA hj).2.2.ksLen
  have htgtsD : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      ∀ i, i < cA.2 → ((d.tgtss m).getD j []).getD i 0 = d.tgts m j i := by
    intro j cA hj i hi
    have hjl : j < (d.ctorsM m).length := (List.getElem?_eq_some_iff.mp hj).1
    have hil : i < (d.ksF m j).length := by rw [hksLen j cA hj]; exact hi
    have h1 : (d.tgtss m).getD j [] = (List.range (d.ksF m j).length).map (d.tgts m j) := by
      show (((List.range (d.ctorsM m).length).map fun j' =>
        (List.range (d.ksF m j').length).map (d.tgts m j')).getD j []) = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hjl]
      rfl
    rw [h1, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hil]
    rfl
  -- ## the member's REAL chains against the leaf's
  have hreal := blockChainsReal_of mp.base2 hm (htgtLt m) hAt
    (fun j cA hj => (hdata m j cA hj).2.2) hρpOf hlenPps hlenIds hX hlenZ hlenZj hC₀ hC hord
  -- ## the fibre law at the member's own index readings
  have hfold : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((d.dsF m j ψ).drop d.nP).map (·.2.2)) bs →
        interp V (consList bs ρ)
            (AnnotTerm.mkAppN (A m ψ) (paramBvars d.nP cA.2 ++ d.esF m j ψ))
          = sumSet (d.w ψ) (sumFibre (d.w ψ)
              (consList (idxValsAt ρ (d.esF m j ψ) bs) ρ)
              (rChains (d.nIdxAt m) (d.nIdxAt m)
                (fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0))
                (essOf (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)))) := by
    intro j cA hj ψ ρ hρ bs hsp
    have hD := (hdata m j cA hj).2.2
    have hlenB : bs.length = cA.2 := by rw [hsp.length_eq]; simp [hD.len ψ]
    have hspE : SpineFit ρ (d.IdsM m ψ) ((d.esF m j ψ).map (interp V (consList bs ρ))) :=
      ((hframes j cA hj).2 ψ ρ (((hframes j cA hj).1 ψ ρ).mp hρ)).2.2 bs hsp
    have hfl := blockFold_of (A := mp.base2.acval (d.memberName m) ψ) hm (hX ψ ρ hρ)
      (hlenPps m ψ hm) rfl hρ
      (fun σ => hAt m (List.getElem?_eq_some_iff.mp hcvTa).1 ψ ρ σ) (hreal ψ ρ hρ) hspE
    have hleafm : mp.base2.acval (d.memberName m) ψ = A m ψ := by rw [hTname]; exact hleafT ψ
    rw [hlenB] at hfl
    rw [paramBvars_eq_paramBvarsAt, ← hleafm, hfl, hlenIds]
    show sumSet _ (sumFibre _ _ (rChains _ _
      (fssOfR d.nP (fixCtorDataList (d.dsF m) (d.esF m) (d.ksF m) (d.eissF m) (d.tssF m) ψ
        (d.ctorsM m) 0))
      (essOfR (fixCtorDataList (d.dsF m) (d.esF m) (d.ksF m) (d.eissF m) (d.tssF m) ψ
        (d.ctorsM m) 0)))) = _
    rw [fssOfR_fixCtorDataList, essOfR_fixCtorDataList]
    rfl
  -- ## the capability laws at every carrier the loop reaches
  have hTlawsOf : ∀ {env' : Env} (m' : EnvModel V env') (kk : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[kk]? = some cA →
      BlockCtorsCore m' d lps cvTasAll p₁ isRec A m →
      FormerData m' cvTa (d.nP + d.nIdxAt m) d.resSort (d.ppsM m) →
      (∀ ψ, m'.acval (d.memberName m) ψ = A m ψ) →
      (∀ ψ, m'.acval cA.1.name ψ = sumMkAV (d.w ψ) kk (d.dsF m kk ψ)
        (((d.dsF m kk ψ).drop d.nP).map (·.2.2))
        (uChains (fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)))) →
      CapsLawsAt m' (d.memberName m) cvTa (ConLeche.blockCapsAt p₁ m isRec) := by
    intro env' m' kk cA hkk hinv' hFD' hleaf' hleafC'
    rw [hTname] at hleaf' ⊢
    by_cases hu : (ConLeche.blockCapsAt p₁ m isRec).unitlike = true
    · refine hcapsU m' kk cA hkk hu hFD' hleaf' (fun ψ => ?_)
      rw [hleafC' ψ, hFssEq ψ]
    · have hU : (ConLeche.blockCapsAt p₁ m isRec).unitlike = false := by simpa using hu
      exact blockCapsLawsAt_vacuous m' hU (hinv'.2.1 m cvTa hcvTa hU)
  -- ## the data's level-parameter invariance and bounds
  have hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ₁ (d.ctorsM m) 0)
        = fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ₂ (d.ctorsM m) 0) := by
    intro ψ₁ ψ₂ hφ
    have hcds : ctorDataList (d.dsF m) (d.esF m) ψ₁ (d.ctorsM m) 0
        = ctorDataList (d.dsF m) (d.esF m) ψ₂ (d.ctorsM m) 0 := by
      refine ctorDataList_params fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ : ∃ cAi, (d.ctorsM m)[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
      exact (hdata m i cAi hi').2.2.params ψ₁ ψ₂
        (fun q hq => hφ q (by rw [← hlpsA cAi (List.mem_of_getElem? hi')]; exact hq))
    rw [hcds]
  have hcdMem : ∀ (ψ : Name → Nat) (i : Nat) (cd : CtorDatum),
      (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)[i]? = some cd →
      ∃ cA, (d.ctorsM m)[i]? = some cA ∧ cd = (cA.1.name, cA.2, d.dsF m i ψ, d.esF m i ψ) := by
    intro ψ i cd hi
    rw [ctorDataList_getElem?, Nat.zero_add] at hi
    cases h : (d.ctorsM m)[i]? with
    | none => rw [h] at hi; exact nomatch hi
    | some cA => rw [h] at hi; exact ⟨cA, rfl, (Option.some.inj hi).symm⟩
  have hFssBelow : ∀ ψ : Name → Nat,
      ∀ Fs ∈ fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0),
        FieldsBelow d.nP Fs := by
    intro ψ Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    obtain ⟨cA, hiA, rfl⟩ := hcdMem ψ i cd hi
    have := (DomsBelow.drop d.nP ((hdata m i cA hiA).2.2.below ψ)).fields
    rwa [Nat.zero_add] at this
  have hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (d.w ψ) ρ (fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)) ∧
      SumFieldsValid ρ (fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)) := by
    intro ψ ρ hρ
    constructor
    · intro Fs hFs
      obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
      obtain ⟨cA, hiA, rfl⟩ := hcdMem ψ i cd hi
      exact ((hframes i cA hiA).2 ψ ρ (((hframes i cA hiA).1 ψ ρ).mp hρ)).1
    · intro Fs hFs
      obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
      obtain ⟨cA, hiA, rfl⟩ := hcdMem ψ i cd hi
      exact ((hframes i cA hiA).2 ψ ρ (((hframes i cA hiA).1 ψ ρ).mp hρ)).2.1
  -- ## the member's constructors, consed
  have hCtors' : ConLeche.checkSumCtors (ConLeche.fueledOps μ F) envI envI (d.memberName m) lps
      d.nP (d.nIdxAt m) d.resSort d.isProp d.large cvTa ctors = .ok (d.ctorsM m, sortss) := by
    rw [hTname]; exact hCtors
  have hout' : ∀ cA ∈ d.ctorsM m, ∀ T'' ∈ d.memberNames, T'' ≠ d.memberName m →
      cA.1.name ∉ ctorsOf T'' := by rw [hTname]; exact hout
  obtain ⟨mp', hE', hfindT', hFD', hleafT', hconsedAt, hinvC⟩ :=
    blockCtorsLoop (T := d.memberName m) (lps := lps) (nP := d.nP) (nIdx := d.nIdxAt m)
      (resSort := d.resSort) (isProp := d.isProp) (large := d.large)
      (names := d.memberNames) (ctorsOf := ctorsOf) (ppsAll := d.ppsM m)
      (idxF := d.idxF m) (dsF := d.dsF m) (esF := d.esF m) (srcsF := d.srcsF m)
      hμ hout' hCtors' hnd hlpsT hlpsA hFssParams hFssBelow
      (fun j cA hj => (hframes j cA hj).1) hFssOkP
      (fun j cA hj ψ ρ hρ bs hsp => ((hframes j cA hj).2 ψ ρ hρ).2.2 bs hsp)
      (fun {env'} m' => BlockCtorsCore m' d lps cvTasAll p₁ isRec A m)
      (fun m' cA A' mC hcA hfresh hac hinv' =>
        hinv'.cons ⟨hnameOf, htgtLt, hctorLt⟩ hfresh (hpshapeA cA hcA) mC hac)
      (ConLeche.blockCapsAt p₁ m isRec) (A m)
      (fun m' kk cA hkk hinv' hFD' hleaf' hleafC' =>
        hTlawsOf m' kk cA hkk hinv' hFD' hleaf' hleafC')
      hfold
      (d.ctorsM m) 0 env mp (fun i => by rw [Nat.zero_add]) (Nat.zero_add _) hE
      (by rw [hTname]; exact hfindT) hFD (fun ψ => by rw [hTname]; exact hleafT ψ)
      (fun i cA hi _ => absurd hi (Nat.not_lt_zero _))
      (fun i cA _ hi => ⟨hfreshC m (Nat.le_refl _) i cA hi, (hdata m i cA hi).1,
        (hdata m i cA hi).2.1, (hdata m i cA hi).2.2.toCtorDataI⟩)
      ⟨hform, hfrP, hdata, hconsed⟩
  -- ## the invariant, one member on
  refine ⟨mp', hE', ⟨hinvC.1, hinvC.2.1, hinvC.2.2.1, fun c hc j cA hj => ?_⟩,
    fun c hc j cA hj => ?_⟩
  · rcases Nat.lt_or_ge c m with hlt | hge
    · exact hinvC.2.2.2 c hlt j cA hj
    · have hcm : c = m := by omega
      subst hcm
      obtain ⟨⟨hfind, hlps, -⟩, -, hleafC⟩ :=
        hconsedAt j cA (List.getElem?_eq_some_iff.mp hj).1 hj
      exact ⟨hfind, hlps, fun ψ => by rw [hleafC ψ, hFssEq ψ]; rfl⟩
  · rw [ConLeche.Semantics.consSumCtors_find?_of_not_mem (hndBlock c (by omega) j cA hj)]
    exact hfreshC c (by omega) j cA hj


/-! ## The loop over the members -/

/-- **What the constructors' stage needs of every member** — the
per-member hypotheses of `stageBlockCtorsAt`, gathered so that the
loop over the `k` members carries ONE obligation. -/
structure BlockCtorsStage (μ : CheckMode) (F : Nat) (d : BlockData V) (lps : List Name)
    (cvTasAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm) (fssZ : (Name → Nat) → Nat → List (List AnnotTerm))
    (envI : Env) (ctorsOf : Name → List Name) : Prop where
  /-- the leaves the `k` formers were consed with -/
  leaf : ∀ (c : Nat) (ψ : Name → Nat), A c ψ
    = blockTyAV d.k (d.w ψ) (fun c' => d.uM c' ψ) (fun c' => d.IdsM c' ψ) d.rss d.tgtss
        (fun c' => d.tlss c' ψ) (fun c' => d.Eiss c' ψ) (fssZ ψ) (fun c' => d.Ess c' ψ)
        (d.ppsM c ψ) c
  /-- every member's constructors, as checked at the formers' environment -/
  ctors : ∀ (m : Nat) (cvTa : ConstantVal), m < d.k → cvTasAll[m]? = some cvTa →
    ∃ (cs : List (ConstantVal × Nat)) (sortss : List (List Level)),
      ConLeche.checkSumCtors (ConLeche.fueledOps μ F) envI envI cvTa.name lps d.nP (d.nIdxAt m)
        d.resSort d.isProp d.large cvTa cs = .ok (d.ctorsM m, sortss)
  nodup : ∀ m, m < d.k → ((d.ctorsM m).map (·.1.name)).Nodup
  out : ∀ (m : Nat) (cvTa : ConstantVal), m < d.k → cvTasAll[m]? = some cvTa →
    ∀ cA ∈ d.ctorsM m, ∀ T'' ∈ d.memberNames, T'' ≠ cvTa.name → cA.1.name ∉ ctorsOf T''
  lpsT : ∀ (m : Nat) (cvTa : ConstantVal), m < d.k → cvTasAll[m]? = some cvTa →
    cvTa.levelParams = lps
  lpsA : ∀ m, m < d.k → ∀ cA ∈ d.ctorsM m, cA.1.levelParams = lps
  pshape : ∀ m, m < d.k → ∀ cA ∈ d.ctorsM m, cA.1.name.isProjFnShape = false
  ndBlock : ∀ m, m < d.k → ∀ (c : Nat), c ≠ m → ∀ (j : Nat) (cB : ConstantVal × Nat),
    (d.ctorsM c)[j]? = some cB → cB.1.name ∉ (d.ctorsM m).map (·.1.name)
  paramsOf : ∀ m, m < d.k → ∀ (ψ : Name → Nat) (ρp : Nat → V),
    Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
    ∀ c, c < d.k → Sat V (((d.ppsM c ψ).take d.nP).map (·.2.2)).reverse ρp
  lenPps : ∀ (c : Nat) (ψ : Name → Nat), c < d.k → (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length
  lenIds : ∀ m, m < d.k → ∀ ψ : Name → Nat, (d.IdsM m ψ).length = d.nIdxAt m
  chainsOk : ∀ m, m < d.k → ∀ (ψ : Name → Nat) (ρp : Nat → V),
    Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
    BlockChainsOk d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) d.rss d.tgtss
      (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fssZ ψ) (fun c => d.Ess c ψ)
  lenZ : ∀ m, m < d.k → ∀ ψ : Name → Nat, (fssZ ψ m).length = (d.ctorsM m).length
  lenZj : ∀ m, m < d.k → ∀ (ψ : Name → Nat) (j : Nat) (cA : ConstantVal × Nat),
    (d.ctorsM m)[j]? = some cA → ((fssZ ψ m).getD j []).length = cA.2
  chainFactsZ : ∀ m, m < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat),
    (d.ctorsM m)[j]? = some cA → ∀ (ψ : Name → Nat) (ρp : Nat → V),
    Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
    ChainFactsB d.k (d.w ψ) d.nP cA.2 ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) m
      (d.ksF m j) ((d.tgtss m).getD j []) ((d.tlss m ψ).getD j []) ((fssZ ψ m).getD j [])
      ((d.Eiss m ψ).getD j []) ((d.Ess m ψ).getD j [])
  chainFacts : ∀ m, m < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat),
    (d.ctorsM m)[j]? = some cA → ∀ (ψ : Name → Nat) (ρp : Nat → V),
    Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
    ChainFactsB d.k (d.w ψ) d.nP cA.2 ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) m
      (d.ksF m j) ((d.tgtss m).getD j []) ((d.tlss m ψ).getD j []) ((d.Fss m ψ).getD j [])
      ((d.Eiss m ψ).getD j []) ((d.Ess m ψ).getD j [])
  ord : ∀ m, m < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
    ∀ (ψ : Name → Nat) (i : Nat), i < cA.2 → ¬ recAt d.nP (d.ksF m j) (d.nP + i) →
    ((d.Fss m ψ).getD j []).getD i default = ((fssZ ψ m).getD j []).getD i default
  frames : ∀ m, m < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((d.dsF m j ψ).take d.nP).map (·.2.2)).reverse ρ) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.dsF m j ψ).take d.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (d.w ψ) ρ (((d.dsF m j ψ).drop d.nP).map (·.2.2)) ∧
        FieldsValid ρ (((d.dsF m j ψ).drop d.nP).map (·.2.2)) ∧
        (∀ bs : List V, SpineFit ρ (((d.dsF m j ψ).drop d.nP).map (·.2.2)) bs →
          SpineFit ρ (d.IdsM m ψ) (idxValsAt ρ (d.esF m j ψ) bs)))
  capsU : ∀ m, m < d.k → ∀ (cvTa : ConstantVal), cvTasAll[m]? = some cvTa →
    ∀ {env' : Env} (m' : EnvModel V env') (kk : Nat) (cA : ConstantVal × Nat),
    (d.ctorsM m)[kk]? = some cA →
    (ConLeche.blockCapsAt p₁ m isRec).unitlike = true →
    FormerData m' cvTa (d.nP + d.nIdxAt m) d.resSort (d.ppsM m) →
    (∀ ψ, m'.acval cvTa.name ψ = A m ψ) →
    (∀ ψ, m'.acval cA.1.name ψ = sumMkAV (d.w ψ) kk (d.dsF m kk ψ)
      (((d.dsF m kk ψ).drop d.nP).map (·.2.2)) (uChains (d.Fss m ψ))) →
    CapsLawsAt m' cvTa.name cvTa (ConLeche.blockCapsAt p₁ m isRec)

/-- **The `k` members' constructors' conses, in block order**
(`consBlockCtors`): `stageBlockCtorsAt` at every member, the core
invariant one member further on at each step. -/
theorem stageBlockCtors (hμ : μ.verifiedChecks = true) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env} {ctorsOf : Name → List Name}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hN : BlockNamesOk (V := V) d cvTasAll)
    (hlenCv : cvTasAll.length = d.k)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTasAll p₁ isRec A fssZ envI ctorsOf)
    (hk : ctorsAs.length = d.k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some (d.ctorsM c)) :
    ∀ (rest : List (List (ConstantVal × Nat))) (i : Nat) (env : Env) (mp : EnvModelM V μ env),
      (∀ c, rest[c]? = ctorsAs[i + c]?) → i + rest.length = ctorsAs.length →
      ConLeche.BlockEtaInv env d.memberNames ctorsOf →
      BlockCtorsCore mp.base2 d lps cvTasAll p₁ isRec A i →
      (∀ c, i ≤ c → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
        env.find? cA.1.name = none) →
      ∃ mp' : EnvModelM V μ (ConLeche.consBlockCtors d.nP rest env),
        ConLeche.BlockEtaInv (ConLeche.consBlockCtors d.nP rest env) d.memberNames ctorsOf ∧
        BlockCtorsCore mp'.base2 d lps cvTasAll p₁ isRec A d.k
  | [], i, env, mp, _, hi, hE, hinv, _ => by
    simp only [List.length_nil, Nat.add_zero] at hi
    rw [hi, hk] at hinv
    exact ⟨mp, hE, hinv⟩
  | ctorsA :: rest, i, env, mp, hrest, hi, hE, hinv, hfresh => by
    have hilt : i < ctorsAs.length := by simp only [List.length_cons] at hi; omega
    have hiA : ctorsAs[i]? = some ctorsA := by
      have := hrest 0; simpa using this.symm
    have hik : i < d.k := by rw [← hk]; exact hilt
    obtain rfl : ctorsA = d.ctorsM i :=
      Option.some.inj ((hiA.symm.trans (hctorsAs i hilt)))
    obtain ⟨cvTa, hcvTa⟩ : ∃ cvTa, cvTasAll[i]? = some cvTa :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hik)⟩
    obtain ⟨cs, sortss, hCtors⟩ := hS.ctors i cvTa hik hcvTa
    obtain ⟨mpI, hE', hinv', hfresh'⟩ :=
      stageBlockCtorsAt hμ hN hik hcvTa hS.leaf hCtors (hS.nodup i hik)
        (hS.out i cvTa hik hcvTa) (hS.lpsT i cvTa hik hcvTa) (hS.lpsA i hik) (hS.pshape i hik)
        (hS.ndBlock i hik) (hS.paramsOf i hik) hS.lenPps (hS.lenIds i hik) (hS.chainsOk i hik)
        (hS.lenZ i hik) (hS.lenZj i hik) (hS.chainFactsZ i hik) (hS.chainFacts i hik)
        (hS.ord i hik) (hS.frames i hik)
        (fun m' kk cA hkk hu hFD' hleaf' hleafC' =>
          hS.capsU i hik cvTa hcvTa m' kk cA hkk hu hFD' hleaf' hleafC')
        mp hE hinv (fun c hc j cA hj => hfresh c hc j cA hj)
    have hrest' : ∀ c, rest[c]? = ctorsAs[i + 1 + c]? := by
      intro c
      have := hrest (c + 1)
      rwa [show i + (c + 1) = i + 1 + c from by omega] at this
    exact stageBlockCtors hμ hN hlenCv hS hk hctorsAs rest (i + 1) _ mpI hrest'
      (by simp only [List.length_cons] at hi; omega) hE' hinv' hfresh'

end ConLeche.Model
