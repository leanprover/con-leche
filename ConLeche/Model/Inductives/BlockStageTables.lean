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

variable {V : Type w} [SetTheory V]

/-- **What a structure-like member's table needs** beyond the
constructors' stage. -/
structure BlockTablesStage (F : Nat) (d : BlockData V) (lps : List Name)
    (formersAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → Term)
    (envI : Env) (sortsOf : Nat → List Level) : Prop
    extends BlockCtorsStage F d lps formersAll p₁ isRec A envI where
  /-- the constructor's parameter-and-field telescope -/
  stripC : ∀ (m : Nat) (ctor : ConstantVal × Nat), m < d.k → d.ctorsM m = [ctor] →
    (ctor.1.type.stripPis (d.nP + ctor.2)).isSome = true
  /-- the block's `Prop` flag is its sort's zeroness -/
  propFlag : d.isProp = (Level.isEquiv d.resSort .zero == some true)
  /-- a member's stored sort, where its type ends in one, is `Prop` with the block's -/
  propZ : d.isProp = true → ∀ (m : Nat) (cvTa : ConstantVal), formersAll[m]? = some cvTa →
    ∀ s, ConLeche.formerResSort cvTa.type = some s → Level.isAlwaysZero s = true
  /-- a member's capability record counts its telescope -/
  capsTele : ∀ m, m < d.k → d.nP + d.nIdxAt m =
    (ConLeche.blockCapsAt p₁ m isRec).nparams + (ConLeche.blockCapsAt p₁ m isRec).nIdx
  /-- no member's name, its recursor's or its constructor's is reserved -/
  resT : ∀ m, m < d.k → ConLeche.reservedBasisNames.contains (d.memberName m) = false
  resR : ∀ m, m < d.k →
    ConLeche.reservedBasisNames.contains ((d.memberName m).str "rec") = false
  resC : ∀ (m : Nat) (ctor : ConstantVal × Nat), m < d.k → d.ctorsM m = [ctor] →
    ConLeche.reservedBasisNames.contains ctor.1.name = false
  /-- the fields' sorts, below the block's -/
  leqF : ∀ (m : Nat) (ctor : ConstantVal × Nat), m < d.k → d.ctorsM m = [ctor] →
    ∀ i, i < ctor.2 → d.isProp = false →
      Level.leq ((sortsOf m).getD i .zero) d.resSort = some true
  /-- the fields are bounded at a non-`Prop` block, and each inhabits its sort -/
  boundF : ∀ (m : Nat) (ctor : ConstantVal × Nat), m < d.k → d.ctorsM m = [ctor] →
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.dsF m 0 ψ).take d.nP)).reverse ρ → d.isProp = false →
      FieldsBound (d.w ψ) ρ (((d.dsF m 0 ψ).drop d.nP))
  /-- the constructors' telescope lengths and bounds -/
  dsLen : ∀ (m j : Nat) (ctor : ConstantVal × Nat), m < d.k → (d.ctorsM m)[j]? = some ctor →
    ∀ ψ, (d.dsF m j ψ).length = d.nP + ctor.2
  dsBelow : ∀ (m j : Nat) (ctor : ConstantVal × Nat), m < d.k → (d.ctorsM m)[j]? = some ctor →
    ∀ ψ, DomsBelow 0 (d.dsF m j ψ)
  /-- a structure-like member's leaf FOLDS to its one constructor's
  fibre (proved at the constructors' stage, where the member's data
  still crosses) -/
  foldT : ∀ (m : Nat) (ctor : ConstantVal × Nat), m < d.k → d.ctorsM m = [ctor] →
    d.nIdxAt m = 0 →
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
      SpineFit ρ ((d.ppsM m ψ)) ts →
      ts.foldl SetTheory.app (interp V ρ (A m ψ))
        = sumSet (d.w ψ) (sumFibre (d.w ψ) (consList ts ρ)
            [((d.dsF m 0 ψ).drop d.nP) ++ [idxEqAV []]])
  sortsF : ∀ (m : Nat) (ctor : ConstantVal × Nat), m < d.k → d.ctorsM m = [ctor] →
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.dsF m 0 ψ).take d.nP)).reverse ρ →
      ∀ j, j < ctor.2 → ∀ as : List V,
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
    (lps : List Name) (formersAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → Term) : Prop :=
  (∀ (c : Nat) (cvTb : ConstantVal), formersAll[c]? = some cvTb →
      FormerInEnv m' cvTb (ConLeche.blockCapsAt p₁ c isRec) ∧
      cvTb.type.constsResolve env = true ∧
      (∀ ψ, m'.acval cvTb.name ψ = A c ψ) ∧
      FormerData m' cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)) ∧
  (∀ (c j : Nat) (ctor : ConstantVal × Nat), (d.ctorsM c)[j]? = some ctor →
      env.find? ctor.1.name = some (.ctorInfo ctor.1 d.nP ctor.2 (d.memberName c)) ∧ ctor.1.levelParams = lps ∧
      ctor.1.type.constsResolve env = true ∧
      (∀ ψ, denote m'.acval env ψ 0 ctor.1.type
        = some (mkPisAV (d.dsF c j ψ)
            (Term.mkAppN (A c ψ) (paramBvars d.nP ctor.2 ++ d.esF c j ψ)))) ∧
      (∀ ψ, m'.acval ctor.1.name ψ = sumMkAV (d.w ψ) j (d.dsF c j ψ)
        (((d.dsF c j ψ).drop d.nP)) (uChains (d.Fss c ψ))))

/-- The constructors' stage's invariant, at the tables' stage. -/
theorem blockTablesCore_of {env : Env} {m' : EnvModel V env} {d : BlockData V}
    {lps : List Name} {formersAll : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → Term}
    (hN : BlockNamesOk (V := V) d formersAll)
    (h : BlockCtorsCore m' d lps formersAll p₁ isRec A d.k) :
    BlockTablesCore m' d lps formersAll p₁ isRec A := by
  obtain ⟨hnameOf, hctorLt, hlenCv⟩ := hN
  obtain ⟨hform, hdata, hconsed⟩ := h
  refine ⟨hform, fun c j ctor hj => ?_⟩
  obtain ⟨hfind, hlps, hleafC⟩ := hconsed c (by
    have := hctorLt c j ctor hj
    omega) j ctor hj
  have hlt : c < d.k := by have := hctorLt c j ctor hj; omega
  obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, formersAll[c]? = some cvTb :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hlt)⟩
  refine ⟨hfind, hlps, (hdata c j ctor hj).1, fun ψ => ?_, hleafC⟩
  have hread := (hdata c j ctor hj).2.2.1.read ψ
  rw [hread]
  show some (mkPisAV _ (ctorBodyAVI m' (d.memberName c) d.nP ctor.2 ψ (d.esF c j ψ))) = _
  unfold ctorBodyAVI
  rw [hnameOf c cvTb hcvTb, (hform c cvTb hcvTb).2.2.1 ψ]


/-- **The tables' invariant survives a table's install.**  No name is
added and no leaf moves, and the table is of a structure that had
none, so every stored lookup and every reading survives. -/
theorem BlockTablesCore.pushTable {env : Env} {m' : EnvModel V env} {d : BlockData V}
    {lps : List Name} {formersAll : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → Term}
    (h : BlockTablesCore m' d lps formersAll p₁ isRec A)
    {tbl : ProjTable} (hT : env.findTable? tbl.structName = none)
    (mC : EnvModel V ⟨env.consts, tbl :: env.tables⟩)
    (hac : mC.acval = m'.acval) :
    BlockTablesCore mC d lps formersAll p₁ isRec A := by
  obtain ⟨hform, hctor⟩ := h
  refine ⟨fun c cvTb hc => ?_, fun c j ctor hj => ?_⟩
  · obtain ⟨hfind, hres, hleaf, hFD⟩ := hform c cvTb hc
    obtain ⟨cvS, hfS, hD⟩ := hfind
    refine ⟨⟨cvS, hfS, hD.pushTable hT mC hac⟩, Expr.constsResolve_of_find (env := env)
      (env' := ⟨env.consts, tbl :: env.tables⟩) (fun _ h => h) hres,
      fun ψ => by rw [hac]; exact hleaf ψ,
      hFD.pushTable hT (constsBound_of_constsResolve _ hres) mC hac⟩
  · obtain ⟨hfind, hlps, hres, hread, hleaf⟩ := hctor c j ctor hj
    refine ⟨hfind, hlps, Expr.constsResolve_of_find (env := env)
      (env' := ⟨env.consts, tbl :: env.tables⟩) (fun _ h => h) hres,
      fun ψ => ?_, fun ψ => by rw [hac]; exact hleaf ψ⟩
    rw [hac]
    exact denote_pushTable_mono hT ψ 0 (constsBound_of_constsResolve _ hres) (hread ψ)


/-- A table installed leaves every other structure's table where it was. -/
theorem findTable?_cons_ne {env : Env} {t : ProjTable} {T : Name} (hne : t.structName ≠ T) :
    (⟨env.consts, t :: env.tables⟩ : Env).findTable? T = env.findTable? T := by
  unfold Env.findTable?
  have hf : (⟨env.consts, t :: env.tables⟩ : Env).find? T = env.find? T := rfl
  rw [hf]
  split
  · simp [hne]
  · rfl

/-- **The block's projection tables** (`blockTables q l = some Q`): `stageFixTable` at every
structure-like member, each table's checks read from the environment they ran at (`E`), the tables'
invariant threaded across the installs. -/
theorem stageBlockTables {F : Nat} {d : BlockData V} {lps : List Name}
    {formersAll : List ConstantVal} {p₁ q : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → Term}
    {envI : Env} {sortsOf : Nat → List Level}
    (hN : BlockNamesOk (V := V) d formersAll)
    (hS : BlockTablesStage (V := V) F d lps formersAll p₁ isRec A envI sortsOf)
    (hqlps : q.lps = lps) (hqnP : q.nP = d.nP)
    {E : Env} {ex : List Name} :
    ∀ (l : List MemberShape) (Q : List ProjTable) (i : Nat) (env : Env) (mp : EnvModelM V env),
      (∀ (c : Nat) (e : MemberShape), l[c]? = some e →
        i + c < d.k ∧ e.cvT.name = d.memberName (i + c) ∧ e.declared.name = e.cvT.name ∧
          e.nIdx = d.nIdxAt (i + c) ∧ e.ctors = d.ctorsM (i + c)) →
      (l.map (·.cvT.name)).Nodup →
      (∀ n ci, E.find? n = some ci → env.find? n = some ci) →
      ConLeche.blockTables q l = some Q →
      (∀ t ∈ Q, ConLeche.checkStructProjTable (m := ConLeche.CheckM) t E = .ok () ∧
        env.findTable? t.structName = none) →
      BlockTablesCore mp.base2 d lps formersAll p₁ isRec A →
      CoverTo mp ex (env.pushDelta [] Q) ex
  | [], Q, i, env, mp, _, _, _, hQ, _, _ => by
    simp only [ConLeche.blockTables, Option.some.injEq] at hQ
    subst hQ
    exact CoverTo.refl mp ex
  | ms :: rest, Q, i, env, mp, hl, hnd, hfE, hQ, hchk, hcore => by
    have hnameOf := hN.1
    have hlenCv := hN.2.2
    obtain ⟨hik, hname, hdecl, hnIdx, hctors⟩ := hl 0 ms rfl
    rw [Nat.add_zero] at hik hname hnIdx hctors
    have hl' : ∀ (c : Nat) (e' : MemberShape), rest[c]? = some e' →
        i + 1 + c < d.k ∧ e'.cvT.name = d.memberName (i + 1 + c) ∧ e'.declared.name = e'.cvT.name ∧
          e'.nIdx = d.nIdxAt (i + 1 + c) ∧ e'.ctors = d.ctorsM (i + 1 + c) := by
      intro c e' hc
      have := hl (c + 1) e' (by simpa using hc)
      rwa [show i + (c + 1) = i + 1 + c from by omega] at this
    have hndR : (rest.map (·.cvT.name)).Nodup := (List.nodup_cons.mp hnd).2
    -- a table is installed only at a member with ONE constructor and no index
    cases hsc : ms.structCtor? with
    | none =>
      rw [ConLeche.blockTables_cons_none hsc] at hQ
      exact stageBlockTables hN hS hqlps hqnP rest Q (i + 1) env mp hl' hndR hfE hQ hchk hcore
    | some ctor =>
    obtain ⟨bodies, Qr, hbodies, hQr, rfl⟩ := ConLeche.blockTables_cons_some hsc hQ
    obtain ⟨hctorsMs, hidx⟩ : ms.ctors = [ctor] ∧ ms.nIdx = 0 := by
      unfold MemberShape.structCtor? at hsc
      split at hsc
      · rename_i c hc
        split at hsc
        · rename_i h0
          obtain rfl := Option.some.inj hsc
          exact ⟨hc, beq_iff_eq.mp h0⟩
        · exact nomatch hsc
      · exact nomatch hsc
    obtain ⟨hT₀, hTfresh⟩ := hchk _ List.mem_cons_self
    have hTenv := ConLeche.checkStructProjTable_mono hfE hTfresh hT₀
    have hnIdx0 : d.nIdxAt i = 0 := by rw [← hnIdx]; exact hidx
    have hctorsEq : d.ctorsM i = [ctor] := hctors.symm.trans hctorsMs
    have hcA0 : (d.ctorsM i)[0]? = some ctor := by rw [hctorsEq]; rfl
    obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, formersAll[i]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hik)⟩
    have hTn : ms.cvT.name = cvTb.name := by rw [hname, hnameOf i cvTb hcvTb]
    have hTn' : d.memberName i = cvTb.name := hnameOf i cvTb hcvTb
    obtain ⟨⟨cvS, hfT, hD⟩, hresTy, hleafT, hFD⟩ := hcore.1 i cvTb hcvTb
    obtain ⟨hfC, hlpsC, -, hCDread, hleafC⟩ := hcore.2 i 0 ctor hcA0
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
    -- the table's install
    rw [hdecl, hqlps, hqnP, hTn] at hTenv
    rw [hdecl, hTn, hqnP] at hbodies
    obtain ⟨mp', hT0, hac⟩ :=
      stageFixTable (pps := d.ppsM i) (ds := d.dsF i 0) (Es := d.esF i 0)
        (L := fun ψ => blockTyG d.k (d.w ψ) (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
          (d.toLfp.holeChains ψ) (d.ppsM i ψ) i)
        mp hTenv hbodies hfT hD
        (hS.lpsT i cvTb hik hcvTb) hfC hlpsC
        (hS.stripC i ctor hik hctorsEq) hS.propFlag
        (fun hp s hs => by
          rcases hD.shows with ⟨hdh, -⟩ | rfl
          · simp [ConLeche.formerDefHeaded, hs] at hdh
          · exact hS.propZ hp i _ hcvTb s hs)
        (by have := hS.capsTele i hik; rwa [hnIdx0, Nat.add_zero] at this)
        (by rw [← hTn']; exact hS.resT i hik)
        (by rw [← hTn']; exact hS.resR i hik)
        (hS.resC i ctor hik hctorsEq)
        (by have := hFD; rwa [hnIdx0, Nat.add_zero] at this)
        (fun ψ => by
          rw [hCDread ψ]
          show _ = some (mkPisAV _ (ctorBodyAVI mp.base2 cvTb.name d.nP ctor.2 ψ (d.esF i 0 ψ)))
          unfold ctorBodyAVI
          rw [hleafT ψ])
        (fun ψ => by rw [hS.dsLen i 0 ctor hik hcA0 ψ])
        (fun ψ => hS.dsBelow i 0 ctor hik hcA0 ψ)
        (hS.leqF i ctor hik hctorsEq)
        (fun ψ => by rw [hleafT ψ, hS.leaf i ψ])
        (fun ψ => by rw [hleafC ψ, hFss1 ψ]; rfl)
        (fun _ => ⟨_, rfl⟩)
        (fun ψ ρ ts hsp => by
          have hf := hS.foldT i ctor hik hctorsEq hnIdx0 ψ ρ ts hsp
          rw [hS.leaf i ψ] at hf
          exact hf)
        (fun ψ ρ => by
          have := (hS.frames i hik 0 ctor hcA0).1 ψ ρ
          rwa [List.take_of_length_le (Nat.le_of_eq (hlenP ψ))] at this)
        (fun ψ ρ hρ => ((hS.frames i hik 0 ctor hcA0).2 ψ ρ hρ).1)
        (hS.boundF i ctor hik hctorsEq) (hS.sortsF i ctor hik hctorsEq)
    -- the invariant, across the table's install
    let tbl : ProjTable := ⟨cvTb.name, lps, d.nP, ctor.1.name, ctor.2, bodies⟩
    have hT' : env.findTable? tbl.structName = none := hT0
    have hcore' : BlockTablesCore mp'.base2 d lps formersAll p₁ isRec A :=
      hcore.pushTable hT' mp'.base2 hac
    -- coverage across the table's install: the carrier rebuilt with the
    -- input's recorded list
    obtain ⟨mk, hb, hL⟩ := EnvModelM.keepLfpOfTable hT' mp' hac
    rw [← hb] at hcore'
    have hEnv : env.pushDelta []
        (⟨ms.declared.name, q.lps, q.nP, ctor.1.name, ctor.2, bodies⟩ :: Qr) =
        (⟨env.consts, tbl :: env.tables⟩ : Env).pushDelta [] Qr := by
      rw [hdecl, hqlps, hqnP, hTn]
      simp [Env.pushDelta, tbl]
    rw [hEnv]
    have hne : ∀ t ∈ Qr, tbl.structName ≠ t.structName := by
      intro t ht hc
      obtain ⟨e, he, hn⟩ := ConLeche.blockTables_names q rest Qr hQr t ht
      obtain ⟨c, hc'⟩ := List.getElem?_of_mem he
      have hm : ms.cvT.name ∈ rest.map (·.cvT.name) := by
        have : ms.cvT.name = e.cvT.name := by
          rw [hTn, ← (hl' c e hc').2.2.1, ← hn]
          exact hc
        rw [this]
        exact List.mem_map_of_mem he
      exact (List.nodup_cons.mp hnd).1 hm
    obtain ⟨mpF, rF, hF⟩ :=
      stageBlockTables hN hS hqlps hqnP rest Qr (i + 1) _ mk hl' hndR hfE hQr
        (fun t ht => ⟨(hchk t (List.mem_cons_of_mem _ ht)).1, by
          rw [findTable?_cons_ne (hne t ht)]
          exact (hchk t (List.mem_cons_of_mem _ ht)).2⟩) hcore'
    have r₀ : CoverRel mp mk := ⟨fun _ _ hn => hn, fun n _ => by rw [hb, hac],
      fun ψ d e ta hbd hta => by
        rw [hb, hac]
        exact denote_pushTable_mono hT' ψ d hbd hta,
      fun D hD => .inl (hL ▸ hD)⟩
    exact ⟨mpF, r₀.trans rF, fun hc => hF (hc.pushTable hL)⟩

end ConLeche.Model
