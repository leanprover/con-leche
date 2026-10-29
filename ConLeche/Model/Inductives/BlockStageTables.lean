module

public import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Cover
public section

/-!
# The projection tables of a block's structure-like members

`stageBlockTables`: the loop `checkBlockTables` runs — a table at
every member with ONE constructor and no index, nothing at any other
member — with `stageFixTable` at each table (abstract in the former's
leaf: here the block's operator leaf `blockTyG` at the member, whose
λ-shape holds by `rfl` and whose fold is the caller's, `foldT`) and
the constructors' stage's invariant (`BlockCtorsCore`) threaded across
the installs.

The threading works because a table's install adds no constant and
moves no leaf, and the table is of a structure that had none — so every
prefix reading, the `k` formers' and constructors' among them, survives
it (`denote_pushTable_mono`).

`BlockTablesStage` is `BlockCtorsStage` plus what a STRUCTURE-LIKE
member's table needs beyond the constructors' stage: the capability
record's η data, the constructor's telescope and its fields' sorts,
and the reserved-name guards.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BlockShape MemberShape ProjTable RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **What a structure-like member's table needs** beyond the
constructors' stage. -/
structure BlockTablesStage (μ : CheckMode) (F : Nat) (d : BlockData V) (lps : List Name)
    (cvTasAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → Term)
    (envI : Env) (ctorsOf : Name → List Name) (sortsOf : Nat → List Level) : Prop
    extends BlockCtorsStage μ F d lps cvTasAll p₁ isRec A envI ctorsOf where
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
      Sat V (((d.dsF m 0 ψ).take d.nP)).reverse ρ → d.isProp = false →
      FieldsBound (d.w ψ) ρ (((d.dsF m 0 ψ).drop d.nP))
  /-- the constructors' telescope lengths and bounds -/
  dsLen : ∀ (m j : Nat) (cA : ConstantVal × Nat), m < d.k → (d.ctorsM m)[j]? = some cA →
    ∀ ψ, (d.dsF m j ψ).length = d.nP + cA.2
  dsBelow : ∀ (m j : Nat) (cA : ConstantVal × Nat), m < d.k → (d.ctorsM m)[j]? = some cA →
    ∀ ψ, DomsBelow 0 (d.dsF m j ψ)
  /-- a structure-like member's leaf FOLDS to its one constructor's
  fibre (proved at the constructors' stage, where the member's data
  still crosses) -/
  foldT : ∀ (m : Nat) (cA : ConstantVal × Nat), m < d.k → d.ctorsM m = [cA] →
    d.nIdxAt m = 0 →
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((d.ppsM m ψ)) ts →
      ts.foldl SetTheory.app (interp V ρ (A m ψ))
        = sumSet (d.w ψ) (sumFibre (d.w ψ) (consList ts ρ)
            [((d.dsF m 0 ψ).drop d.nP) ++ [idxEqAV []]])
  sortsF : ∀ (m : Nat) (cA : ConstantVal × Nat), m < d.k → d.ctorsM m = [cA] →
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.dsF m 0 ψ).take d.nP)).reverse ρ →
      ∀ j, j < cA.2 → ∀ as : List V,
        SpineFit ρ ((((d.dsF m 0 ψ).drop d.nP)).take j) as →
        interp V (consList as ρ) ((((d.dsF m 0 ψ).drop d.nP)).getD j default)
          ∈ˢ (univ (((sortsOf m).getD j .zero).eval ψ) : V)

/-- **What the tables' loop threads**: the `k` formers with their
leaves and telescope readings, and the constructors stored with their
readings and leaves.  It is
what `BlockCtorsCore` gives (`blockTablesCore_of`) minus the
constructors' full data — a table's cons crosses a TYPE's reading,
not an arbitrary term's. -/
@[expose] def BlockTablesCore {env : Env} (m' : EnvModel V env) (d : BlockData V)
    (lps : List Name) (cvTasAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → Term) : Prop :=
  (∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      cvTb.type.constsResolve env = true ∧
      (∀ ψ, m'.acval cvTb.name ψ = A c ψ) ∧
      FormerData m' cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)) ∧
  (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      env.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2) ∧ cA.1.levelParams = lps ∧
      cA.1.type.constsResolve env = true ∧
      (∀ ψ, denote m'.acval env ψ 0 cA.1.type
        = some (mkPisAV (d.dsF c j ψ)
            (Term.mkAppN (A c ψ) (paramBvars d.nP cA.2 ++ d.esF c j ψ)))) ∧
      (∀ ψ, m'.acval cA.1.name ψ = sumMkAV (d.w ψ) j (d.dsF c j ψ)
        (((d.dsF c j ψ).drop d.nP)) (uChains (d.Fss c ψ))))

/-- The constructors' stage's invariant, at the tables' stage. -/
theorem blockTablesCore_of {env : Env} {m' : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → Term}
    (hN : BlockNamesOk (V := V) d cvTasAll)
    (h : BlockCtorsCore m' d lps cvTasAll p₁ isRec A d.k) :
    BlockTablesCore m' d lps cvTasAll p₁ isRec A := by
  obtain ⟨hnameOf, hctorLt, hlenCv⟩ := hN
  obtain ⟨hform, hdata, hconsed⟩ := h
  refine ⟨hform, fun c j cA hj => ?_⟩
  obtain ⟨hfind, hlps, hleafC⟩ := hconsed c (by
    have := hctorLt c j cA hj
    omega) j cA hj
  have hlt : c < d.k := by have := hctorLt c j cA hj; omega
  obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTasAll[c]? = some cvTb :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hlt)⟩
  refine ⟨hfind, hlps, (hdata c j cA hj).1, fun ψ => ?_, hleafC⟩
  have hread := (hdata c j cA hj).2.2.1.read ψ
  rw [hread]
  show some (mkPisAV _ (ctorBodyAVI m' (d.memberName c) d.nP cA.2 ψ (d.esF c j ψ))) = _
  unfold ctorBodyAVI
  rw [hnameOf c cvTb hcvTb, (hform c cvTb hcvTb).2.2.1 ψ]


/-- **The tables' invariant survives a table's install.**  No name is
added and no leaf moves, and the table is of a structure that had
none, so every stored lookup and every reading survives. -/
theorem BlockTablesCore.pushTable {env : Env} {m' : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → Term}
    (h : BlockTablesCore m' d lps cvTasAll p₁ isRec A)
    {tbl : ProjTable} (hT : env.findTable? tbl.structName = none)
    (mC : EnvModel V ⟨env.consts, tbl :: env.tables⟩)
    (hac : mC.acval = m'.acval) :
    BlockTablesCore mC d lps cvTasAll p₁ isRec A := by
  obtain ⟨hform, hctor⟩ := h
  refine ⟨fun c cvTb hc => ?_, fun c j cA hj => ?_⟩
  · obtain ⟨hfind, hres, hleaf, hFD⟩ := hform c cvTb hc
    refine ⟨hfind, Expr.constsResolve_of_find (env := env)
      (env' := ⟨env.consts, tbl :: env.tables⟩) (fun _ h => h) hres,
      fun ψ => by rw [hac]; exact hleaf ψ,
      hFD.pushTable hT (constsBound_of_constsResolve _ hres) mC hac⟩
  · obtain ⟨hfind, hlps, hres, hread, hleaf⟩ := hctor c j cA hj
    refine ⟨hfind, hlps, Expr.constsResolve_of_find (env := env)
      (env' := ⟨env.consts, tbl :: env.tables⟩) (fun _ h => h) hres,
      fun ψ => ?_, fun ψ => by rw [hac]; exact hleaf ψ⟩
    rw [hac]
    exact denote_pushTable_mono hT ψ 0 (constsBound_of_constsResolve _ hres) (hread ψ)


/-- **The block's projection tables**: `stageFixTable` at every
structure-like member, the tables' invariant threaded across the
installs. -/
theorem stageBlockTables {F : Nat} {d : BlockData V} {lps : List Name}
    {cvTasAll : List ConstantVal} {p₁ q : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → Term}
    {envI : Env} {ctorsOf : Name → List Name} {sortsOf : Nat → List Level}
    (hN : BlockNamesOk (V := V) d cvTasAll)
    (hS : BlockTablesStage (V := V) μ F d lps cvTasAll p₁ isRec A envI ctorsOf sortsOf)
    (hqlps : q.lps = lps) (hqnP : q.nP = d.nP) (hqres : q.resSort = d.resSort)
    {ex : List Name} :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) (i : Nat)
      (env env₂ : Env) (mp : EnvModelM V μ env),
      (∀ (c : Nat) (e : MemberShape × List (ConstantVal × Nat) × List (List Level)),
        l[c]? = some e → i + c < d.k ∧ e.1.cvT.name = d.memberName (i + c) ∧
          e.1.nIdx = d.nIdxAt (i + c) ∧ e.2.1 = d.ctorsM (i + c) ∧
          ∀ sorts, e.2.2 = [sorts] → sorts = sortsOf (i + c)) →
      ConLeche.checkBlockTables (m := ConLeche.CheckM) q l env = .ok env₂ →
      BlockTablesCore mp.base2 d lps cvTasAll p₁ isRec A →
      CoverTo mp ex env₂ ex
  | [], i, env, env₂, mp, _, h, _ => by
    obtain rfl : env₂ = env := Except.ok.inj h.symm
    exact CoverTo.refl mp ex
  | e :: rest, i, env, env₂, mp, hl, h, hcore => by
    have hnameOf := hN.1
    have hlenCv := hN.2.2
    obtain ⟨hik, hname, hnIdx, hctors, hsorts⟩ := hl 0 e rfl
    rw [Nat.add_zero] at hik hname hnIdx hctors hsorts
    have hl' : ∀ (c : Nat) (e' : MemberShape × List (ConstantVal × Nat) × List (List Level)),
        rest[c]? = some e' → i + 1 + c < d.k ∧ e'.1.cvT.name = d.memberName (i + 1 + c) ∧
          e'.1.nIdx = d.nIdxAt (i + 1 + c) ∧ e'.2.1 = d.ctorsM (i + 1 + c) ∧
          ∀ sorts, e'.2.2 = [sorts] → sorts = sortsOf (i + 1 + c) := by
      intro c e' hc
      have := hl (c + 1) e' (by simpa using hc)
      rwa [show i + (c + 1) = i + 1 + c from by omega] at this
    obtain ⟨ms, ctorsA, sortss⟩ := e
    simp only at hname hnIdx hctors hsorts
    -- a table is consed only at a member with ONE constructor and no index
    cases ctorsA with
    | nil =>
      rw [ConLeche.checkBlockTables] at h
      · exact stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) env env₂ mp hl' h hcore
      · simp
    | cons cA ctl =>
    cases ctl with
    | cons c2 ctl2 =>
      rw [ConLeche.checkBlockTables] at h
      · exact stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) env env₂ mp hl' h hcore
      · simp
    | nil =>
    cases sortss with
    | nil =>
      rw [ConLeche.checkBlockTables] at h
      · exact stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) env env₂ mp hl' h hcore
      · simp
    | cons sorts stl =>
    cases stl with
    | cons s2 stl2 =>
      rw [ConLeche.checkBlockTables] at h
      · exact stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) env env₂ mp hl' h hcore
      · simp
    | nil =>
    rw [ConLeche.checkBlockTables] at h
    by_cases hidx : (ms.nIdx == 0) = true
    case neg =>
      rw [ite_eq_right hidx] at h
      exact stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) env env₂ mp hl' h hcore
    case pos =>
    rw [ite_eq_left hidx] at h
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
    obtain ⟨hfC, hlpsC, -, hCDread, hleafC⟩ := hcore.2 i 0 cA hcA0
    have hlenP : ∀ ψ : Name → Nat, (d.ppsM i ψ).length = d.nP := by
      intro ψ; have := hFD.len ψ; rwa [hnIdx0, Nat.add_zero] at this
    have hFss1 : ∀ ψ : Name → Nat,
        d.Fss i ψ = [((d.dsF i 0 ψ).drop d.nP)] := by
      intro ψ
      have hlen : (d.Fss i ψ).length = 1 := by
        show (fssOfR _ _).length = 1
        rw [fssOfR_length]
        show (fixCtorDataList _ _ _ _ _ _ _ _).length = 1
        rw [fixCtorDataList_length, hctorsEq]; rfl
      obtain ⟨Fs, hFs⟩ := List.length_eq_one_iff.mp hlen
      have h0 : (d.Fss i ψ).getD 0 [] = ((d.dsF i 0 ψ).drop d.nP) :=
        fssOfR_fixCtorDataList_getD hcA0
      rw [hFs] at h0 ⊢
      simp only [List.getD_cons_zero] at h0
      rw [h0]
    -- the table's cons
    cases hT : ConLeche.checkStructProjTable (m := ConLeche.CheckM) ms.cvT.name cA.1.name
        q.lps q.nP cA.2 q.resSort (ConLeche.structProjGuards cA.1.type q.nP cA.2 (sortsOf i))
        cA.1 env with
    | error er => rw [hT] at h; exact nomatch h
    | ok env' =>
    rw [hT] at h
    rw [hqlps, hqnP, hqres, hTn] at hT
    obtain ⟨tbl, mp', henv, hstructN, hT0, hac⟩ :=
      stageFixTable (pps := d.ppsM i) (ds := d.dsF i 0) (Es := d.esF i 0)
        (L := fun ψ => blockTyG d.k (d.w ψ) (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
          (d.toLfp.holeChains ψ) (d.ppsM i ψ) i)
        mp hT hfT
        (hS.etaData i cA hik hctorsEq) (hS.lpsT i cvTb hik hcvTb) hfC hlpsC
        (hS.stripC i cA hik hctorsEq) hS.propFlag
        (by rw [← hTn']; exact hS.resT i hik)
        (by rw [← hTn']; exact hS.resR i hik)
        (hS.resC i cA hik hctorsEq)
        (by have := hFD; rwa [hnIdx0, Nat.add_zero] at this)
        (fun ψ => by
          rw [hCDread ψ]
          show _ = some (mkPisAV _ (ctorBodyAVI mp.base2 cvTb.name d.nP cA.2 ψ (d.esF i 0 ψ)))
          unfold ctorBodyAVI
          rw [hleafT ψ])
        (fun ψ => by rw [hS.dsLen i 0 cA hik hcA0 ψ])
        (fun ψ => hS.dsBelow i 0 cA hik hcA0 ψ)
        (hS.leqF i cA hik hctorsEq)
        (fun ψ => by rw [hleafT ψ, hS.leaf i ψ])
        (fun ψ => by rw [hleafC ψ, hFss1 ψ]; rfl)
        (fun _ => ⟨_, rfl⟩)
        (fun ψ ρ ts hsp => by
          have hf := hS.foldT i cA hik hctorsEq hnIdx0 ψ ρ ts hsp
          rw [hS.leaf i ψ] at hf
          exact hf)
        (fun ψ ρ => by
          have := (hS.frames i hik 0 cA hcA0).1 ψ ρ
          rwa [List.take_of_length_le (Nat.le_of_eq (hlenP ψ))] at this)
        (fun ψ ρ hρ => ((hS.frames i hik 0 cA hcA0).2 ψ ρ hρ).1)
        (hS.boundF i cA hik hctorsEq) (hS.sortsF i cA hik hctorsEq)
    -- the invariant, across the table's install
    subst henv
    have hT' : env.findTable? tbl.structName = none := by rw [hstructN]; exact hT0
    have hcore' : BlockTablesCore mp'.base2 d lps cvTasAll p₁ isRec A :=
      hcore.pushTable hT' mp'.base2 hac
    -- coverage across the table's install: the carrier rebuilt with the
    -- input's recorded list
    obtain ⟨mk, hb, hL⟩ := EnvModelM.keepLfpOfTable hT' mp' hac
    rw [← hb] at hcore'
    obtain ⟨mpF, hagF, hF⟩ :=
      stageBlockTables hN hS hqlps hqnP hqres rest (i + 1) _ env₂ mk hl' h hcore'
    have hagk : Agrees mp mk := fun n hn => ⟨hn, by rw [hb, hac]⟩
    exact ⟨mpF, hagk.trans hagF, fun hc => hF (hc.pushTable hL)⟩

end ConLeche.Model
