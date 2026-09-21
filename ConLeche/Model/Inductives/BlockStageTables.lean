module

public import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Inductives.BlockStageTable
public section

/-!
# The projection tables of a block's structure-like members (task #315 M3)

`stageBlockTables`: the loop `checkBlockTables` runs — a table at
every member with ONE constructor and no index, nothing at any other
member — with `stageBlockTable` at each table and the constructors'
stage's invariant (`BlockCtorsCore`) threaded across the conses.

Threading is what made the table stage's conclusion change
(`FixStageTable.lean`): a table's cons is one `projInfo` constant, its
name fresh, and the carrier's leaves are the old ones off that name —
so the `k` formers' and constructors' readings, and the other members'
`NoProjEnv`, cross it.

`BlockTablesStage` is `BlockCtorsStage` plus what a STRUCTURE-LIKE
member's table needs beyond the constructors' stage: the capability
record's η data, the constructor's telescope and its fields' sorts,
and the reserved-name and projection-shape guards.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BlockShape MemberShape ProjTable BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **What a structure-like member's table needs** beyond the
constructors' stage. -/
structure BlockTablesStage (μ : CheckMode) (F : Nat) (d : BlockData V) (lps : List Name)
    (cvTasAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm) (fssZ : (Name → Nat) → Nat → List (List AnnotTerm))
    (envI : Env) (ctorsOf : Name → List Name) (sortsOf : Nat → List Level) : Prop
    extends BlockCtorsStage μ F d lps cvTasAll p₁ isRec A fssZ envI ctorsOf where
  /-- the η data a structure-like member's record carries -/
  etaData : ∀ (m : Nat) (cA : ConstantVal × Nat), m < d.k → d.ctorsM m = [cA] →
    (ConLeche.blockCapsAt p₁ m isRec).eta = true →
    (Level.isEquiv d.resSort .zero == some true) = false ∧
    (ConLeche.blockCapsAt p₁ m isRec).etaCtor = cA.1.name ∧
    (ConLeche.blockCapsAt p₁ m isRec).etaParams = d.nP ∧
    (ConLeche.blockCapsAt p₁ m isRec).etaFields = cA.2
  /-- the constructor's parameter-and-field telescope -/
  stripC : ∀ (m : Nat) (cA : ConstantVal × Nat), m < d.k → d.ctorsM m = [cA] →
    (cA.1.type.stripPis (d.nP + cA.2)).isSome = true
  /-- the block's `Prop` flag is its sort's zeroness -/
  propFlag : d.isProp = (Level.isEquiv d.resSort .zero == some true)
  /-- no member's name, and no constructor's, is a projection function's -/
  shapeT : ∀ m, m < d.k → (d.memberName m).isProjFnShape = false
  /-- no member's name, its recursor's or its constructor's is reserved -/
  resT : ∀ m, m < d.k → ConLeche.reservedBasisNames.contains (d.memberName m) = false
  resR : ∀ m, m < d.k →
    ConLeche.reservedBasisNames.contains ((d.memberName m).str "rec") = false
  resC : ∀ (m : Nat) (cA : ConstantVal × Nat), m < d.k → d.ctorsM m = [cA] →
    ConLeche.reservedBasisNames.contains cA.1.name = false
  /-- the fields' sorts, below the block's -/
  leqF : ∀ (m : Nat) (cA : ConstantVal × Nat), m < d.k → d.ctorsM m = [cA] →
    ∀ i, i < cA.2 → d.isProp = false →
      Level.leq ((sortsOf m).getD i .zero) d.resSort = some true
  /-- the fields are bounded at a non-`Prop` block, and each inhabits its sort -/
  boundF : ∀ (m : Nat) (cA : ConstantVal × Nat), m < d.k → d.ctorsM m = [cA] →
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.dsF m 0 ψ).take d.nP).map (·.2.2)).reverse ρ → d.isProp = false →
      FieldsBound (d.w ψ) ρ (((d.dsF m 0 ψ).drop d.nP).map (·.2.2))
  /-- the constructors' telescope lengths and bounds -/
  dsLen : ∀ (m j : Nat) (cA : ConstantVal × Nat), m < d.k → (d.ctorsM m)[j]? = some cA →
    ∀ ψ, (d.dsF m j ψ).length = d.nP + cA.2
  dsBelow : ∀ (m j : Nat) (cA : ConstantVal × Nat), m < d.k → (d.ctorsM m)[j]? = some cA →
    ∀ ψ, DomsBelow 0 (d.dsF m j ψ)
  /-- a structure-like member's leaf FOLDS to its one constructor's
  fibre (`blockFoldSingle` at the constructors' stage, where the
  member's data still crosses) -/
  foldT : ∀ (m : Nat) (cA : ConstantVal × Nat), m < d.k → d.ctorsM m = [cA] →
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((d.ppsM m ψ).map (·.2.2)) ts →
      ts.foldl SetTheory.app (interp V ρ (A m ψ))
        = sumSet (d.w ψ) (sumFibre (d.w ψ) (consList ts ρ)
            [((d.dsF m 0 ψ).drop d.nP).map (·.2.2) ++ [idxEqAV []]])
  /-- no member's projections occur in a stored former's type … -/
  noProjT : ∀ (m c : Nat) (cvTb : ConstantVal), m < d.k → cvTasAll[c]? = some cvTb →
    ∀ i, Expr.NoProjAt (d.memberName m) i cvTb.type
  /-- … nor in a stored constructor's … -/
  noProjC : ∀ (m c j : Nat) (cA : ConstantVal × Nat), m < d.k → (d.ctorsM c)[j]? = some cA →
    ∀ i, Expr.NoProjAt (d.memberName m) i cA.1.type
  /-- … nor in ANOTHER member's projection-table bodies -/
  noProjB : ∀ (m c : Nat) (cA : ConstantVal × Nat) (bodies : Array Expr), m < d.k → c < d.k →
    c ≠ m → d.ctorsM c = [cA] →
    ConLeche.structProjBodies (d.memberName c) d.nP cA.2 cA.1.type = some bodies →
    ∀ (i j : Nat), Expr.NoProjAt (d.memberName m) i (bodies.getD j default)
  sortsF : ∀ (m : Nat) (cA : ConstantVal × Nat), m < d.k → d.ctorsM m = [cA] →
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.dsF m 0 ψ).take d.nP).map (·.2.2)).reverse ρ →
      ∀ j, j < cA.2 → ∀ as : List V,
        SpineFit ρ ((((d.dsF m 0 ψ).drop d.nP).map (·.2.2)).take j) as →
        interp V (consList as ρ) ((((d.dsF m 0 ψ).drop d.nP).map (·.2.2)).getD j default)
          ∈ˢ (univ (((sortsOf m).getD j .zero).eval ψ) : V)

/-- **What the tables' loop threads**: the `k` formers with their
leaves and telescope readings, the constructors stored with their
readings and leaves, and every member's projection slots free.  It is
what `BlockCtorsCore` gives (`blockTablesCore_of`) minus the
constructors' full data — a table's cons crosses a TYPE's reading,
not an arbitrary term's. -/
@[expose] def BlockTablesCore {env : Env} (m' : EnvModel V env) (d : BlockData V)
    (lps : List Name) (cvTasAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm) (nc : Nat) : Prop :=
  (∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      cvTb.type.constsResolve env = true ∧
      (∀ ψ, m'.acval cvTb.name ψ = A c ψ) ∧
      FormerData m' cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)) ∧
  (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      env.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2) ∧ cA.1.levelParams = lps ∧
      cA.1.type.constsResolve env = true ∧
      (∀ ψ, denoteMeta m'.acval env ψ 0 cA.1.type
        = some (mkPisAV (d.dsF c j ψ)
            (AnnotTerm.mkAppN (A c ψ) (paramBvars d.nP cA.2 ++ d.esF c j ψ)))) ∧
      (∀ ψ, m'.acval cA.1.name ψ = sumMkAV (d.w ψ) j (d.dsF c j ψ)
        (((d.dsF c j ψ).drop d.nP).map (·.2.2)) (uChains (d.Fss c ψ)))) ∧
  ∀ c, nc ≤ c → c < d.k → ∀ j, NoProjEnv env (d.memberName c) j

/-- The constructors' stage's invariant, at the tables' stage. -/
theorem blockTablesCore_of {env : Env} {m' : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    (hN : BlockNamesOk (V := V) d cvTasAll)
    (h : BlockCtorsCore m' d lps cvTasAll p₁ isRec A d.k)
    (hnp : ∀ c, c < d.k → ∀ j, NoProjEnv env (d.memberName c) j) :
    BlockTablesCore m' d lps cvTasAll p₁ isRec A 0 := by
  obtain ⟨hnameOf, -, hctorLt, hlenCv⟩ := hN
  obtain ⟨hform, -, hdata, hconsed⟩ := h
  refine ⟨hform, fun c j cA hj => ?_, fun c _ hc j => hnp c hc j⟩
  obtain ⟨hfind, hlps, hleafC⟩ := hconsed c (by
    have := hctorLt c j cA hj
    omega) j cA hj
  have hlt : c < d.k := by have := hctorLt c j cA hj; omega
  obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTasAll[c]? = some cvTb :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hlt)⟩
  refine ⟨hfind, hlps, (hdata c j cA hj).1, fun ψ => ?_, hleafC⟩
  have hread := (hdata c j cA hj).2.2.read ψ
  rw [hread]
  show some (mkPisAV _ (ctorBodyAVI m' (d.memberName c) d.nP cA.2 ψ (d.esF c j ψ))) = _
  unfold ctorBodyAVI
  rw [hnameOf c cvTb hcvTb, (hform c cvTb hcvTb).2.2.1 ψ]


/-- **The tables' invariant survives a table's cons.**  A stored name
is not the fresh table's, the readings cross the head's slots
(`ConsCrossAt` at a table is exactly "the consed structure's
projections do not occur"), and every LATER member's slots stay free
— the consed table's bodies are the member's own. -/
theorem BlockTablesCore.consTable {env : Env} {m' : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {mm : Nat}
    (h : BlockTablesCore m' d lps cvTasAll p₁ isRec A mm)
    {tbl : ProjTable} (hstruct : tbl.structName = d.memberName mm)
    (hfresh : env.find? (ConstantInfo.projInfo tbl).name = none)
    (hnoT : ∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      ∀ i, Expr.NoProjAt (d.memberName mm) i cvTb.type)
    (hnoC : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      ∀ i, Expr.NoProjAt (d.memberName mm) i cA.1.type)
    (hnoB : ∀ c, mm + 1 ≤ c → c < d.k → ∀ (i j : Nat), j < tbl.numFields →
      Expr.NoProjAt (d.memberName c) i (tbl.bodies.getD j default))
    (mC : EnvModel V ⟨.projInfo tbl :: env.consts⟩)
    (hac : mC.acval = acvalWith m'.acval (ConstantInfo.projInfo tbl).name (fun _ => .sort 0)) :
    BlockTablesCore mC d lps cvTasAll p₁ isRec A (mm + 1) := by
  obtain ⟨hform, hctor, hnp⟩ := h
  have hne : ∀ n : Name, (env.find? n).isSome = true →
      ¬ ((ConstantInfo.projInfo tbl).name = n) := by
    intro n hn hnn
    rw [← hnn, hfresh] at hn
    exact nomatch hn
  refine ⟨fun c cvTb hc => ?_, fun c j cA hj => ?_, fun c hc hck j => ?_⟩
  · obtain ⟨hfind, hres, hleaf, hFD⟩ := hform c cvTb hc
    have hcross : ConsCrossAt (.projInfo tbl) cvTb.type := by
      intro tbl' heq i
      obtain rfl := ConstantInfo.projInfo.inj heq
      rw [hstruct]
      exact hnoT c cvTb hc i
    refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfind, Expr.constsResolve_mono hres,
      fun ψ => ?_, hFD.cross (c₀ := .projInfo tbl) hfresh hcross
        (constsBound_of_constsResolve _ hres) mC hac⟩
    rw [hac]
    show acvalWith m'.acval (ConstantInfo.projInfo tbl).name _ cvTb.name ψ = _
    rw [acvalWith_ne (fun hh => hne cvTb.name (by rw [hfind]; rfl) hh.symm)]
    exact hleaf ψ
  · obtain ⟨hfind, hlps, hres, hread, hleaf⟩ := hctor c j cA hj
    have hcross : ConsCrossAt (.projInfo tbl) cA.1.type := by
      intro tbl' heq i
      obtain rfl := ConstantInfo.projInfo.inj heq
      rw [hstruct]
      exact hnoC c j cA hj i
    refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfind, hlps, Expr.constsResolve_mono hres,
      fun ψ => ?_, fun ψ => ?_⟩
    · rw [hac]
      exact denoteMeta_cons_mono hfresh hcross ψ 0
        (constsBound_of_constsResolve _ hres) (hread ψ)
    · rw [hac]
      show acvalWith m'.acval (ConstantInfo.projInfo tbl).name _ cA.1.name ψ = _
      rw [acvalWith_ne (fun hh => hne cA.1.name (by rw [hfind]; rfl) hh.symm)]
      exact hleaf ψ
  · refine (hnp c (by omega) hck j).cons ⟨?_, (fun _ _ _ hh => nomatch hh),
      (fun _ _ _ _ hh => nomatch hh), fun tbl' heq j' hj' => ?_⟩
    · show Expr.NoProjAt (d.memberName c) j (Expr.sort (.succ .zero))
      simp
    · obtain rfl := ConstantInfo.projInfo.inj heq
      exact hnoB c hc hck j j' hj'


/-- **The block's projection tables**: `stageBlockTable` at every
structure-like member, the tables' invariant threaded across the
conses. -/
theorem stageBlockTables {F : Nat} {d : BlockData V} {lps : List Name}
    {cvTasAll : List ConstantVal} {p₁ q : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)}
    {envI : Env} {ctorsOf : Name → List Name} {sortsOf : Nat → List Level}
    (hN : BlockNamesOk (V := V) d cvTasAll)
    (hS : BlockTablesStage (V := V) μ F d lps cvTasAll p₁ isRec A fssZ envI ctorsOf sortsOf)
    (hqlps : q.lps = lps) (hqnP : q.nP = d.nP) (hqres : q.resSort = d.resSort) :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) (i : Nat)
      (env env₂ : Env) (mp : EnvModelM V μ env),
      (∀ (c : Nat) (e : MemberShape × List (ConstantVal × Nat) × List (List Level)),
        l[c]? = some e → i + c < d.k ∧ e.1.cvT.name = d.memberName (i + c) ∧
          e.1.nIdx = d.nIdxAt (i + c) ∧ e.2.1 = d.ctorsM (i + c) ∧
          ∀ sorts, e.2.2 = [sorts] → sorts = sortsOf (i + c)) →
      ConLeche.checkBlockTables (m := ConLeche.CheckM) q l env = .ok env₂ →
      BlockTablesCore mp.base2 d lps cvTasAll p₁ isRec A i →
      Nonempty (EnvModelM V μ env₂)
  | [], i, env, env₂, mp, _, h, _ => by
    obtain rfl : env₂ = env := Except.ok.inj h.symm
    exact ⟨mp⟩
  | e :: rest, i, env, env₂, mp, hl, h, hcore => by
    have hnameOf := hN.1
    have hlenCv := hN.2.2.2
    obtain ⟨hik, hname, hnIdx, hctors, hsorts⟩ := hl 0 e rfl
    rw [Nat.add_zero] at hik hname hnIdx hctors hsorts
    have hl' : ∀ (c : Nat) (e' : MemberShape × List (ConstantVal × Nat) × List (List Level)),
        rest[c]? = some e' → i + 1 + c < d.k ∧ e'.1.cvT.name = d.memberName (i + 1 + c) ∧
          e'.1.nIdx = d.nIdxAt (i + 1 + c) ∧ e'.2.1 = d.ctorsM (i + 1 + c) ∧
          ∀ sorts, e'.2.2 = [sorts] → sorts = sortsOf (i + 1 + c) := by
      intro c e' hc
      have := hl (c + 1) e' (by simpa using hc)
      rwa [show i + (c + 1) = i + 1 + c from by omega] at this
    -- the invariant weakens: this member's table is the last one that may
    -- touch its own slots
    have hcoreW : BlockTablesCore mp.base2 d lps cvTasAll p₁ isRec A (i + 1) :=
      ⟨hcore.1, hcore.2.1, fun c hc hck j => hcore.2.2 c (by omega) hck j⟩
    obtain ⟨ms, ctorsA, sortss⟩ := e
    simp only at hname hnIdx hctors hsorts
    -- a table is consed only at a member with ONE constructor and no index
    cases ctorsA with
    | nil =>
      rw [ConLeche.checkBlockTables] at h
      · exact stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) env env₂ mp hl' h hcoreW
      · simp
    | cons cA ctl =>
    cases ctl with
    | cons c2 ctl2 =>
      rw [ConLeche.checkBlockTables] at h
      · exact stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) env env₂ mp hl' h hcoreW
      · simp
    | nil =>
    cases sortss with
    | nil =>
      rw [ConLeche.checkBlockTables] at h
      · exact stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) env env₂ mp hl' h hcoreW
      · simp
    | cons sorts stl =>
    cases stl with
    | cons s2 stl2 =>
      rw [ConLeche.checkBlockTables] at h
      · exact stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) env env₂ mp hl' h hcoreW
      · simp
    | nil =>
    rw [ConLeche.checkBlockTables] at h
    by_cases hidx : (ms.nIdx == 0) = true
    case neg =>
      rw [if_neg hidx] at h
      exact stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) env env₂ mp hl' h hcoreW
    case pos =>
    rw [if_pos hidx] at h
    -- the member is structure-like
    have hnIdx0 : d.nIdxAt i = 0 := by rw [← hnIdx]; exact beq_iff_eq.mp hidx
    have hctorsEq : d.ctorsM i = [cA] := hctors.symm
    have hcA0 : (d.ctorsM i)[0]? = some cA := by rw [hctorsEq]; rfl
    have hsortsEq : sorts = sortsOf i := hsorts sorts rfl
    subst hsortsEq
    obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTasAll[i]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hik)⟩
    have hTn : ms.cvT.name = cvTb.name := by rw [hname, hnameOf i cvTb hcvTb]
    have hTn' : d.memberName i = cvTb.name := hnameOf i cvTb hcvTb
    obtain ⟨hfT, hresTy, hleafT, hFD⟩ := hcore.1 i cvTb hcvTb
    obtain ⟨hfC, hlpsC, -, hCDread, hleafC⟩ := hcore.2.1 i 0 cA hcA0
    have hlenP : ∀ ψ : Name → Nat, (d.ppsM i ψ).length = d.nP := by
      intro ψ; have := hFD.len ψ; rwa [hnIdx0, Nat.add_zero] at this
    have hFss1 : ∀ ψ : Name → Nat,
        d.Fss i ψ = [((d.dsF i 0 ψ).drop d.nP).map (·.2.2)] := by
      intro ψ
      have hlen : (d.Fss i ψ).length = 1 := by
        show (fssOfR _ _).length = 1
        rw [fssOfR_length]
        show (fixCtorDataList _ _ _ _ _ _ _ _).length = 1
        rw [fixCtorDataList_length, hctorsEq]; rfl
      obtain ⟨Fs, hFs⟩ := List.length_eq_one_iff.mp hlen
      have h0 : (d.Fss i ψ).getD 0 [] = ((d.dsF i 0 ψ).drop d.nP).map (·.2.2) :=
        fssOfR_fixCtorDataList_getD hcA0
      rw [hFs] at h0 ⊢
      simp only [List.getD_cons_zero] at h0
      rw [h0]
    -- the table's cons
    cases hT : ConLeche.checkStructProjTable (m := ConLeche.CheckM) ms.cvT.name cA.1.name
        q.lps q.nP cA.2 q.resSort (ConLeche.structProjGuards cA.1.type q.nP cA.2 (sortsOf i))
        1 cA.1 env with
    | error er => rw [hT] at h; exact nomatch h
    | ok env' =>
    rw [hT] at h
    rw [hqlps, hqnP, hqres, hTn] at hT
    obtain ⟨bodies, hbodies, -, -, hfreshTbl, henvOut⟩ := ConLeche.checkStructProjTable_inv hT
    obtain ⟨tbl, mp', henv, hstructN, hfreshT, hac⟩ :=
      stageBlockTable (k := d.k) (m := i) (pps := d.ppsM i) (ds := d.dsF i 0) (Es := d.esF i 0)
        (ufOf := fun ψ c => d.uM c ψ) (IdssOf := fun ψ c => d.IdsM c ψ)
        (rsssOf := fun _ => d.rss) (tgtsssOf := fun _ => d.tgtss)
        (tlsssOf := fun ψ c => d.tlss c ψ) (EisssOf := fun ψ c => d.Eiss c ψ)
        (FsssOf := fun ψ => fssZ ψ) (EsssOf := fun ψ c => d.Ess c ψ)
        mp hT hfT
        (hS.etaData i cA hik hctorsEq) (hS.lpsT i cvTb hik hcvTb) hfC hlpsC
        (hS.stripC i cA hik hctorsEq) hS.propFlag
        (by rw [← hTn']; exact hS.shapeT i hik)
        (hS.pshape i hik cA (by rw [hctorsEq]; exact List.mem_singleton_self _))
        (by rw [← hTn']; exact hS.resT i hik)
        (by rw [← hTn']; exact hS.resR i hik)
        (hS.resC i cA hik hctorsEq)
        (by rw [← hTn']; exact hcore.2.2 i (Nat.le_refl _) hik)
        (by have := hFD; rwa [hnIdx0, Nat.add_zero] at this)
        (fun ψ => by
          rw [hCDread ψ]
          show _ = some (mkPisAV _ (ctorBodyAVI mp.base2 cvTb.name d.nP cA.2 ψ (d.esF i 0 ψ)))
          unfold ctorBodyAVI
          rw [hleafT ψ])
        (fun ψ => by rw [hS.dsLen i 0 cA hik hcA0 ψ])
        (fun ψ => hS.dsBelow i 0 cA hik hcA0 ψ)
        (hS.leqF i cA hik hctorsEq)
        (fun ψ => by rw [hleafT ψ, hS.leaf i ψ]; rfl)
        (fun ψ => by rw [hleafC ψ, hFss1 ψ]; rfl)
        (fun ψ ρ ts hsp => by
          have hf := hS.foldT i cA hik hctorsEq ψ ρ ts hsp
          rw [hS.leaf i ψ] at hf
          exact hf)
        (fun ψ ρ => by
          have := (hS.frames i hik 0 cA hcA0).1 ψ ρ
          rwa [List.take_of_length_le (Nat.le_of_eq (hlenP ψ))] at this)
        (fun ψ ρ hρ => ⟨((hS.frames i hik 0 cA hcA0).2 ψ ρ hρ).1,
          ((hS.frames i hik 0 cA hcA0).2 ψ ρ hρ).2.1⟩)
        (hS.boundF i cA hik hctorsEq) (hS.sortsF i cA hik hctorsEq)
    -- the table's own shape, from the check
    have htblB : tbl.bodies = bodies ∧ tbl.numFields = cA.2 := by
      have heq := henvOut.symm.trans henv
      simp only [Env.mk.injEq, List.cons.injEq, ConstantInfo.projInfo.injEq] at heq
      obtain ⟨heq', -⟩ := heq
      exact ⟨by rw [← heq'], by rw [← heq']⟩
    -- the invariant, across the table's cons
    subst henv
    have hcore' : BlockTablesCore mp'.base2 d lps cvTasAll p₁ isRec A (i + 1) :=
      hcore.consTable (by rw [hstructN]; exact hTn'.symm) hfreshT
        (fun c cvTc hc j => hS.noProjT i c cvTc hik hc j)
        (fun c j cB hj k => hS.noProjC i c j cB hik hj k)
        (fun c hc hck k j hj => by
          rw [htblB.1]
          exact hS.noProjB c i cA bodies hck hik (by omega) hctorsEq
            (by rw [hTn']; exact hbodies) k j)
        mp'.base2 hac
    exact stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) _ env₂ mp' hl' h hcore'

end ConLeche.Model
