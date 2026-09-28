module

public import ConLeche.Model.Inductives.BlockStageCtors
public import ConLeche.Model.Annot.BlockLfpTup
public import ConLeche.Model.Annot.LfpHoleOp
public import ConLeche.Model.Cover
public import ConLeche.SetModel.Access
public import ConLeche.Kernel.Inductives.BlockParts

public section

/-!
# What the member block's stage reads of the positivity/class check

`MemberPosFacts`: the ONE seam between an inductive block's positivity
evidence and the constructors' stage (`blockTablesStage_of`) plus the
block step's operator facts (`declBlock`).  It carries exactly what those
consumers take from the check's run, stated about ANY datum that agrees
with the block (`MemberPosFit`) at ANY model of the formers' environment
— never about the run itself:

* `occ`  — M2′: the canonical crest of a stored constructor names no
  member constant (at the canonical holes);
* `link` — the member constructor's WALKED normal form (`d.nfFF`, the
  check's output) and its declared crest read as Π-towers with the
  datum's body, the fields reading alike on the hole context; the normal
  form names only stored constants, no member (M3), only the block's
  levels; and the stored field shape facts (U4, the result indices) of
  its fields;
* `grade` — U2: the fields with holes are closed, graded, bit-valid and
  (at a `Type`-valued block) small at the hole frame of every tuple;
* `pos`  — every member constructor positive along the tuple order
  (`CtorPos (tupRel …)`), under coverage at the carrier;
* `acc`  — the hole operator accessible with a bound of the level, the
  (W) premise `closed_of_acc` consumes.

`BlockAbsRead` and `StoredFieldShapes` at a datum follow from `link`
(`MemberPosFacts.absRead`, `MemberPosFacts.storedShapes`).

Producers: today the positivity check's run (`memberPosFacts_of_run`,
`MemberPosRun.lean`); after the flip, the class check (PROOFPLAN T2:
`link`, `occ`; T7: `pos`; T8: `acc`; T9: `grade`).  Nothing here
mentions the run, a derivation, a frame or a node.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal BlockParts BlockShape instPisWith)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The walk context's facts -/

/-- **What a member constructor's walk context reads of the carrier**:
the `k` formers stored with their data, and every constructor's reading
— no constructor need be stored yet (`BlockCtorsCore` gives it at any
stage, `BlockCtorsCore.holeCtx`; the formers' pass gives it at the dummy
carrier). -/
@[expose] def BlockHoleCtxFacts {env : Env} (m : EnvModel V env) (d : BlockData V)
    (lps : List Name) (cvTas : List ConstantVal) (p₁ : BlockShape) (isRec : Bool) : Prop :=
  (∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      FormerData m cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)) ∧
  (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      BlockCtorRead m d lps c j cA ∧ BlockAbsRead m d lps c j cA)

theorem BlockCtorsCore.holeCtx {env : Env} {m : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (h : BlockCtorsCore m d lps cvTas p₁ isRec A nc) : BlockHoleCtxFacts m d lps cvTas p₁ isRec :=
  ⟨fun c cvTb hc => ⟨(h.1 c cvTb hc).1, (h.1 c cvTb hc).2.2.2⟩,
    fun c j cA hj => ⟨(h.2.2.1 c j cA hj).2.2.1, (h.2.2.1 c j cA hj).2.2.2⟩⟩

/-! ## The record -/

/-- **A datum is the block's, at the check's normal forms**: the block's
parts `p`, its stored constructors `ctorsAs` and the check's walked
normal forms `nfs` agree with the datum `d` at the level parameters
`lps`. -/
structure MemberPosFit (d : BlockData V) (lps : List Name) (p : BlockParts)
    (ctorsAs : List (List (ConstantVal × Nat))) (nfs : List (List Expr)) : Prop where
  hnames : p.memberNames = d.memberNames
  hlps : p.lps = lps
  hnP : p.nP = d.nP
  hnIdxs : p.nIdxs = d.nIdxs
  hres : p.resSort = d.resSort
  hk : d.k = d.memberNames.length
  hnd : d.memberNames.Nodup
  hinst : d.nInst = 0
  hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c)
  hlenCA : ctorsAs.length = d.k
  hclosed : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
    cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true
  hnfs : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
    d.nfFF c j = (nfs.getD c []).getD j default

/-- **The member block's positivity facts** (see the module docstring):
what the constructors' stage and the block step read of the check, at
the formers' environment `env`, for the block `p` with formers `cvTas`,
stored constructors `ctorsAs` and walked normal forms `nfs`. -/
structure MemberPosFacts (V : Type w) [SetTheory V] (μ : ConLeche.CheckMode) (env : Env)
    (p : BlockParts) (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (nfs : List (List Expr)) : Prop where
  /-- M2′ at the canonical holes. -/
  occ : ∀ {d : BlockData V} {lps : List Name}, MemberPosFit d lps p ctorsAs nfs →
    ∀ c, c < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      (canonAbs d.memberNames lps d.nP d.k cA.1.type).nestOcc d.memberNames 0 0 = false
  /-- The walked normal form, read at a model. -/
  link : ∀ (mp : EnvModelM V μ env) {d : BlockData V} {lps : List Name} {p₁ : BlockShape}
    {isRec : Bool}, MemberPosFit d lps p ctorsAs nfs → BlockNamesOk (V := V) d cvTas →
    (∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      FormerData mp.base2 cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)) →
    ∀ (ψ : Name → Nat), (∀ t, t < d.k → ∃ cv caps bs s,
      env.find? (d.memberName t) = some (.indInfo cv caps) ∧ cv.levelParams = lps ∧
      cv.type.stripPis (d.nP + d.nIdxAt t) = some (bs, .sort s) ∧ s.eval ψ = d.w ψ) →
    ∀ {c j : Nat} {cA : ConstantVal × Nat}, c < d.k → (d.ctorsM c)[j]? = some cA →
    StoredCtorFacts mp.base2 (d.memberName c) lps cA.1 d.nP cA.2 (d.fvsPF c j)
      (d.xFvsF c j) (d.xrestF c j) (d.idxF c j) (d.dsF c j) (d.esF c j) →
    ConstsBound env (d.nfFF c j) ∧
    (d.nfFF c j).nestOcc d.memberNames 0 0 = false ∧
    lpDefF lps (d.nfFF c j) = true ∧
    ∃ (A : Expr) (abD abN : List (Nat × Nat × AnnotTerm)),
      instPisWith (canonParams d.nP) (canonAbs d.memberNames lps d.nP d.k cA.1.type) = some A ∧
      denoteMeta mp.base2.acval env ψ (d.nP + d.k) A
        = some (mkPisAV abD (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      denoteMeta mp.base2.acval env ψ (d.nP + d.k) (d.nfFF c j)
        = some (mkPisAV abN (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      abD.length = cA.2 ∧ abN.length = cA.2 ∧
      abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) ∧
      FieldsEqOn V (d.holeCtx ψ).reverse (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
      StoredFieldShapes V d.k d.nP (d.w ψ) d.nIdxAt (fun t => mp.base2.acval (d.memberName t) ψ)
        (d.params ψ).reverse (abN.map (·.2.2)) ((d.Fss c ψ).getD j [])
  /-- U2: the fields with holes graded at the hole frame of every tuple. -/
  grade : ∀ (mp : EnvModelM V μ env) {d : BlockData V} {lps : List Name} {p₁ : BlockShape}
    {isRec : Bool}, MemberPosFit d lps p ctorsAs nfs → BlockNamesOk (V := V) d cvTas →
    BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec →
    ∀ (ψ : Name → Nat) {c : Nat}, c < d.N → ∀ {j : Nat}, j < (d.ctorsM c).length →
    (FieldsBelow (d.nP + d.k) (d.absF ψ c j) ∧
      ∀ e ∈ d.absE ψ c j, Term.bvarsBelow (d.nP + d.k + (d.absF ψ c j).length) e.erase) ∧
    ∀ (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X : Nat → V, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
    FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j) ∧
    FieldsValid (d.toLfp.frame ψ ρp X) (d.absF ψ c j) ∧
    ∀ fs : List V, SpineFit (d.toLfp.frame ψ ρp X) (d.absF ψ c j) fs →
      ∀ e ∈ d.absE ψ c j, WellDenotedV V (consList fs (d.toLfp.frame ψ ρp X)) e
  /-- Positivity along the tuple order, under coverage at the carrier. -/
  pos : ∀ (mp : EnvModelM V μ env) {d : BlockData V} {lps : List Name} {p₁ : BlockShape}
    {isRec : Bool}, MemberPosFit d lps p ctorsAs nfs → BlockNamesOk (V := V) d cvTas →
    BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec →
    (∃ mk : EnvModelM V μ env, mk.base2 = mp.base2 ∧ LfpCover mk p.memberNames) →
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
        d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j
  /-- Accessibility of the hole operator at a `Type`-valued frame. -/
  acc : ∀ (mp : EnvModelM V μ env) {d : BlockData V} {lps : List Name} {p₁ : BlockShape}
    {isRec : Bool}, MemberPosFit d lps p ctorsAs nfs → BlockNamesOk (V := V) d cvTas →
    BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec → BlockHoleFacts mp.base2 d lps →
    (∃ mk : EnvModelM V μ env, mk.base2 = mp.base2 ∧ LfpCover mk p.memberNames) →
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp → d.w ψ ≠ 0 →
    (∀ c, c < d.N → IdxOk (d.uM c ψ) ρp (d.IdsM c ψ)) →
    (∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j)) →
    ∃ A, A ∈ˢ (univ (d.toLfp.w ψ) : V) ∧
      AccTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) d.toLfp.N (d.toLfp.idx ψ ρp)
        (d.toLfp.holeOp ψ ρp) A

/-! ## The datum's reading facts, from `link` -/

namespace MemberPosFacts

variable {μ : ConLeche.CheckMode} {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nfs : List (List Expr)}

/-- **The reading fact at a uniform block's datum** — at a datum whose
fields with holes are the normal forms' readings at the model
(`habs`). -/
theorem absRead (h : MemberPosFacts V μ env p cvTas ctorsAs nfs) (mp : EnvModelM V μ env)
    {d : BlockData V} {lps : List Name} {p₁ : BlockShape} {isRec : Bool}
    (hfit : MemberPosFit d lps p ctorsAs nfs) (hN : BlockNamesOk (V := V) d cvTas)
    (hF : ∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      FormerData mp.base2 cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c))
    (hformers : ∀ (ψ : Name → Nat) (t : Nat), t < d.k → ∃ cv caps bs s,
      env.find? (d.memberName t) = some (.indInfo cv caps) ∧ cv.levelParams = lps ∧
      cv.type.stripPis (d.nP + d.nIdxAt t) = some (bs, .sort s) ∧ s.eval ψ = d.w ψ)
    {c j : Nat} {cA : ConstantVal × Nat} (hc : c < d.k) (hcj : (d.ctorsM c)[j]? = some cA)
    (hD : StoredCtorFacts mp.base2 (d.memberName c) lps cA.1 d.nP cA.2 (d.fvsPF c j)
      (d.xFvsF c j) (d.xrestF c j) (d.idxF c j) (d.dsF c j) (d.esF c j))
    (habs : ∀ ψ, d.absF ψ c j
      = nfFieldsRead mp.base2.acval env (d.nP + d.k) cA.2 (d.nfFF c j) ψ) :
    BlockAbsRead mp.base2 d lps c j cA := by
  obtain ⟨hcb, -, -, A, -, -, hA, -⟩ :=
    h.link mp hfit hN hF (fun _ => 0) (hformers _) hc hcj hD
  refine ⟨hcb, A, hA, fun ψ => ?_⟩
  obtain ⟨-, -, -, A', abD, abN, hA', hRD, hRN, hlD, hlN, hbits, hEq, -⟩ :=
    h.link mp hfit hN hF ψ (hformers ψ) hc hcj hD
  rw [hA] at hA'
  obtain rfl := Option.some.inj hA'
  have habN : abN.map (·.2.2) = d.absF ψ c j := by
    rw [habs ψ]; exact (nfFieldsRead_eq hRN hlN).symm
  refine ⟨abD, abN, hRD, hRN, hlD, hlN, hbits, habN, ?_⟩
  rw [← habN]
  exact hEq

/-- **The stored field shape facts at a uniform block's datum**: the
normal form reads as the Π-tower over the datum's fields with holes (the
datum's reading fact), so `link`'s fields with holes ARE the datum's. -/
theorem storedShapes (h : MemberPosFacts V μ env p cvTas ctorsAs nfs) (mp : EnvModelM V μ env)
    {d : BlockData V} {lps : List Name} {p₁ : BlockShape} {isRec : Bool}
    (hfit : MemberPosFit d lps p ctorsAs nfs) (hN : BlockNamesOk (V := V) d cvTas)
    (hcore : BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec) (ψ : Name → Nat)
    (hformers : ∀ t, t < d.k → ∃ cv caps bs s,
      env.find? (d.memberName t) = some (.indInfo cv caps) ∧ cv.levelParams = lps ∧
      cv.type.stripPis (d.nP + d.nIdxAt t) = some (bs, .sort s) ∧ s.eval ψ = d.w ψ)
    {c : Nat} (hc : c < d.N) {j : Nat} (hj : j < (d.ctorsM c).length) :
    StoredFieldShapes V d.k d.nP (d.w ψ) d.nIdxAt (fun t => mp.base2.acval (d.memberName t) ψ)
      (d.params ψ).reverse (d.absF ψ c j) ((d.Fss c ψ).getD j []) := by
  have hck : c < d.k := by
    have : c < d.k + d.nInst := hc
    rw [hfit.hinst] at this
    omega
  have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
  generalize hcA : (d.ctorsM c)[j] = cA at hcj
  obtain ⟨hCf, hCb⟩ := hfit.hclosed c j cA hcj
  have hD₀ : BlockCtorDataI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := (hcore.2 c j cA hcj).1
  obtain ⟨-, -, -, A, abD, abN, -, -, hRN, -, hlN, -, -, hS⟩ :=
    h.link mp hfit hN hcore.1 ψ hformers hck hcj (hD₀.storedCtorFacts hCf hCb)
  -- the datum's reading of the same normal form
  obtain ⟨-, A₀, -, hR⟩ := (hcore.2 c j cA hcj).2
  obtain ⟨-, abN', -, hNr, -, hlN', -, habN, -⟩ := hR ψ
  rw [hRN] at hNr
  obtain ⟨rfl, -⟩ := mkPisAV_inj (hlN.trans hlN'.symm) (Option.some.inj hNr)
  rw [habN] at hS
  exact hS

end MemberPosFacts

end ConLeche.Model
