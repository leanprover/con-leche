module

import ConLeche.Model.Inductives.BlockCtorFuns
public import ConLeche.Model.Inductives.BlockLeafOk
import ConLeche.Model.Inductives.BlockStageFormer
import ConLeche.Model.Inductives.BlockCaps
import ConLeche.Model.Inductives.FixZeroField
import ConLeche.Verify.Inductives.BlockInv
public section

/-!
# The uniform block install's assembly, stage by stage (task #315 M3)

`declNative`'s `DeclNative.lean:120–560` at `k` members: what the
formers' run yields (`blockFormerFacts_of`), the members' index
telescopes (`blockIdxFacts_of`), and — the two former passes — the
DUMMY pass at the empty chains, at whose carrier every member's
constructors are read (`blockCtorFuns_of`), and the REAL pass at the
fixpoint leaves those readings build.

**Why the members' sorts are a datum here.**  `checkBlockTele` reads
member `m`'s result sort off ITS OWN telescope and `checkBlockInds`
completes the record with member 0's, the agreement between them being
`Level.isEquiv` — so a member's former strips to `.sort (sOf m)`, and
only the VALUE of that sort is the block's (`BlockFormerFacts.sEval`).
Everything the model needs of a sort is its value, which is why
`FormerData` transports (`FormerData.congr_sort`) and why the
constructors' data producers take the former's own sort.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BlockShape BlockParts MemberShape BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## A former's data reads its sort's VALUE -/

/-- **`FormerData` transports along a sort of the same value.**  The
record mentions the sort only through `resSort.eval`, which is what
official's `Level.isEquiv` agreement between the members pins. -/
theorem FormerData.congr_sort {env : Env} {m : EnvModel V env} {cvT : ConstantVal}
    {nP : Nat} {s s' : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : FormerData m cvT nP s pps) (hs : ∀ ψ : Name → Nat, s.eval ψ = s'.eval ψ) :
    FormerData m cvT nP s' pps where
  read ψ := by rw [← hs ψ]; exact h.read ψ
  len := h.len
  bits := h.bits
  okTy ψ ρ := by rw [← hs ψ]; exact h.okTy ψ ρ
  below := h.below
  params ψ₁ ψ₂ hφ := ⟨(h.params ψ₁ ψ₂ hφ).1, by rw [← hs ψ₁, ← hs ψ₂]; exact (h.params ψ₁ ψ₂ hφ).2⟩

/-! ## The k formers' run -/

/-- **What the `k` formers' run yields at the pre-block environment**:
every member's checked former with its name, level parameters,
freshness and syntactic guards, its telescope stripped at its OWN
result sort (`sOf`), its reading (`FormerData`, at the BLOCK's sort by
`sEval`), and official's parameter agreement read semantically. -/
structure BlockFormerFacts {env : Env} (mp : EnvModelM V μ env) (q : BlockShape)
    (cvTas : List ConstantVal) (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (sOf : Nat → Level) : Prop where
  /-- one former per member -/
  lenCv : cvTas.length = q.k
  /-- a member's former carries its name and the block's level parameters -/
  nameOf : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
    cvTa.name = q.memberNames.getD m .anonymous
  lpsOf : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa → cvTa.levelParams = q.lps
  /-- the pre-block environment has no member -/
  freshOf : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
    env.find? cvTa.name = none
  resolveOf : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
    cvTa.type.constsResolve env = true
  nresOf : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
    ConLeche.reservedBasisNames.contains cvTa.name = false
  pshapeOf : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
    cvTa.name.isProjFnShape = false
  tyWFOf : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
    cvTa.type.hasFvar = false ∧
    cvTa.type.allLevelParamsDefined cvTa.levelParams = true ∧
    cvTa.type.looseBVarsBounded 0 = true
  /-- the member's telescope, stripped at its OWN result sort -/
  stripOf : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
    ∃ bs : List (Expr × BinderMeta),
      cvTa.type.stripPis (q.nP + q.nIdxs.getD m 0) = some (bs, .sort (sOf m))
  /-- and that sort's VALUE is the block's (official's `Level.isEquiv`) -/
  sEval : ∀ (m : Nat) (ψ : Name → Nat), (sOf m).eval ψ = q.resSort.eval ψ
  /-- the member's telescope reading -/
  fdOf : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
    FormerData mp.base2 cvTa (q.nP + q.nIdxs.getD m 0) q.resSort (ppsOf m)
  /-- off the block the reading is the empty telescope (the leaves are
  a TOTAL function of the position, and the stages' obligations are
  stated at every position) -/
  ppsNil : ∀ m : Nat, cvTas[m]? = none → ∀ ψ : Name → Nat, ppsOf m ψ = []
  /-- **official's parameter agreement, semantically**: the members'
  parameter telescopes are interchangeable at a frame -/
  paramsIff : ∀ m₁ m₂, m₁ < q.k → m₂ < q.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (((ppsOf m₁ ψ).take q.nP).map (·.2.2)).reverse ρ ↔
      Sat V (((ppsOf m₂ ψ).take q.nP).map (·.2.2)).reverse ρ



/-- **The formers' run yields the members' data.**  Member `m`'s
former is `cvTas[m]`, checked at the PRE-block environment (official
stores none before all `k` are checked); `sOf m` is the sort its own
telescope ends in, and `sEval` is official's `Level.isEquiv`
agreement, read through the level semantics. -/
theorem blockFormerFacts_of (hμ : μ.verifiedChecks = true) {F : Nat} {env envI : Env}
    {p₀ : BlockParts} {isRec : Bool} {cvTas : List ConstantVal} {q : BlockShape}
    (mp : EnvModelM V μ env)
    (h : ConLeche.checkBlockInds (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p₀ isRec
      = .ok (envI, cvTas, q))
    (hlps : ∀ ms ∈ p₀.members, ms.cvT.levelParams = p₀.lps) :
    ∃ (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (sOf : Nat → Level),
      BlockFormerFacts mp q cvTas ppsOf sOf := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hmem0, hcvTas, rfl, -, htele0, hteles, hagree⟩ :=
    ConLeche.checkBlockInds_shape h
  have hmembers : (p₀.toBlockShape.withSort s0).members = ms0 :: rest := hmem0
  obtain ⟨cvsAll, hcvsAll⟩ : ∃ l : List (ConstantVal × Level), l = (cvTa0, s0) :: cvs := ⟨_, rfl⟩
  obtain ⟨sOf, hsOfDef⟩ : ∃ f : Nat → Level, f = fun m => ((cvsAll[m]?).map (·.2)).getD s0 :=
    ⟨_, rfl⟩
  have hsOfAt : ∀ (m : Nat) (r : ConstantVal × Level), cvsAll[m]? = some r → sOf m = r.2 := by
    intro m r hr
    rw [hsOfDef]
    show ((cvsAll[m]?).map (·.2)).getD s0 = r.2
    rw [hr]; rfl
  have hsOfNone : ∀ m : Nat, cvsAll[m]? = none → sOf m = s0 := by
    intro m hm
    rw [hsOfDef]
    show ((cvsAll[m]?).map (·.2)).getD s0 = s0
    rw [hm]; rfl
  have hmap : cvTas = cvsAll.map (·.1) := by rw [hcvTas, hcvsAll]; rfl
  obtain ⟨hlenCvs, hteleAt⟩ := ConLeche.checkBlockTeles_inv hteles
  -- every member's run, off ONE list of (former, sort) pairs
  have hrunAt : ∀ (m : Nat) (ms : MemberShape),
      (p₀.toBlockShape.withSort s0).members[m]? = some ms →
      ∃ r : ConstantVal × Level, cvsAll[m]? = some r ∧
        ConLeche.checkBlockTele (ConLeche.fueledOps μ F) env p₀.nP ms = .ok r ∧
        ∀ ψ : Name → Nat, r.2.eval ψ = s0.eval ψ := by
    intro m ms hms
    rw [hmembers] at hms
    match m with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hms
      subst hms
      exact ⟨(cvTa0, s0), by rw [hcvsAll]; rfl, htele0, fun _ => rfl⟩
    | j + 1 =>
      simp only [List.getElem?_cons_succ] at hms
      obtain ⟨r, hr, hrun⟩ := hteleAt j ms hms
      refine ⟨r, by rw [hcvsAll]; simpa using hr, hrun, fun ψ => ?_⟩
      obtain ⟨hiso, -⟩ := ConLeche.checkBlockAgree_inv hagree r (List.mem_of_getElem? hr)
      exact Level.isEquiv_sound (beq_iff_eq.mp hiso) ψ
  have hsEval : ∀ (m : Nat) (ψ : Name → Nat),
      (sOf m).eval ψ = (p₀.toBlockShape.withSort s0).resSort.eval ψ := by
    intro m ψ
    show (sOf m).eval ψ = s0.eval ψ
    cases hm : cvsAll[m]? with
    | none => rw [hsOfNone m hm]
    | some r =>
      rw [hsOfAt m r hm]
      -- the entry belongs to a member's run
      rcases m with _ | j
      · rw [hcvsAll] at hm
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
        rw [← hm]
      · rw [hcvsAll] at hm
        simp only [List.getElem?_cons_succ] at hm
        obtain ⟨hiso, -⟩ := ConLeche.checkBlockAgree_inv hagree r (List.mem_of_getElem? hm)
        exact Level.isEquiv_sound (beq_iff_eq.mp hiso) ψ
  -- the members' names and index counts, read off the record
  have hnIdxAt : ∀ (m : Nat) (ms : MemberShape),
      (p₀.toBlockShape.withSort s0).members[m]? = some ms →
      (p₀.toBlockShape.withSort s0).nIdxs.getD m 0 = ms.nIdx := by
    intro m ms hms
    show ((p₀.toBlockShape.withSort s0).members.map (·.nIdx)).getD m 0 = ms.nIdx
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hms]; rfl
  have hnameAt : ∀ (m : Nat) (ms : MemberShape),
      (p₀.toBlockShape.withSort s0).members[m]? = some ms →
      (p₀.toBlockShape.withSort s0).memberNames.getD m .anonymous = ms.cvT.name := by
    intro m ms hms
    show ((p₀.toBlockShape.withSort s0).members.map (·.cvT.name)).getD m .anonymous = ms.cvT.name
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hms]; rfl
  -- a former, with its member's record entry and its own run
  have hpair : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
      ∃ ms : MemberShape, (p₀.toBlockShape.withSort s0).members[m]? = some ms ∧
        ConLeche.checkBlockTele (ConLeche.fueledOps μ F) env p₀.nP ms = .ok (cvTa, sOf m) := by
    intro m cvTa hm
    rw [hmap, List.getElem?_map] at hm
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hm
    have hml : m < (p₀.toBlockShape.withSort s0).members.length := by
      have hlt : m < cvsAll.length := (List.getElem?_eq_some_iff.mp hr).1
      rw [hcvsAll] at hlt
      rw [hmembers]
      simp only [List.length_cons] at hlt ⊢
      rw [hlenCvs] at hlt
      exact hlt
    obtain ⟨ms, hms⟩ : ∃ ms, (p₀.toBlockShape.withSort s0).members[m]? = some ms :=
      ⟨_, List.getElem?_eq_getElem hml⟩
    obtain ⟨r', hr', hrun, -⟩ := hrunAt m ms hms
    have hrr : r' = r := Option.some.inj (hr'.symm.trans hr)
    rw [hrr] at hrun
    refine ⟨ms, hms, ?_⟩
    rw [hsOfAt m r hr]
    exact hrun
  -- the syntactic facts of one member's former
  have hsyn : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
      ∃ (ms : MemberShape) (bs : List (Expr × BinderMeta)),
        (p₀.toBlockShape.withSort s0).members[m]? = some ms ∧
        cvTa.name = ms.cvT.name ∧ cvTa.levelParams = ms.cvT.levelParams ∧
        env.find? cvTa.name = none ∧
        ConLeche.reservedBasisNames.contains cvTa.name = false ∧
        cvTa.name.isProjFnShape = false ∧
        cvTa.type.constsResolve env = true ∧
        cvTa.type.hasFvar = false ∧
        cvTa.type.allLevelParamsDefined cvTa.levelParams = true ∧
        cvTa.type.looseBVarsBounded 0 = true ∧
        cvTa.type.stripPis (p₀.nP + ms.nIdx) = some (bs, .sort (sOf m)) ∧
        ∃ pps : (Name → Nat) → List (Nat × Nat × AnnotTerm),
          FormerData mp.base2 cvTa (p₀.nP + ms.nIdx) (sOf m) pps := by
    intro m cvTa hm
    obtain ⟨ms, hms, hrun⟩ := hpair m cvTa hm
    obtain ⟨cvT, hn, hl, hccv, bs, hst⟩ := ConLeche.checkBlockTele_shape hrun
    obtain ⟨hfind, hnres, hpsh, -, hlbt, hitf, type', -, -, hann, hlpd, htr, -, -, rfl⟩ :=
      ConLeche.checkConstantVal_inv hccv
    obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
    obtain ⟨pps, hFD⟩ := formerData_of hμ mp hccv hst
    exact ⟨ms, bs, hms, hn, hl, hfind, hnres, hpsh,
      htr, htf', hlpd, hbt', hst, pps, hFD⟩
  -- the members' telescope readings, chosen positionally
  have hfdEx : ∀ m : Nat, ∃ pps : (Name → Nat) → List (Nat × Nat × AnnotTerm),
      (∀ cvTa : ConstantVal, cvTas[m]? = some cvTa →
        FormerData mp.base2 cvTa
          ((p₀.toBlockShape.withSort s0).nP
            + (p₀.toBlockShape.withSort s0).nIdxs.getD m 0)
          (p₀.toBlockShape.withSort s0).resSort pps) ∧
      (cvTas[m]? = none → ∀ ψ : Name → Nat, pps ψ = []) := by
    intro m
    cases hm : cvTas[m]? with
    | none =>
      refine ⟨fun _ => [], fun _ hh => ?_, fun _ _ => rfl⟩
      exact absurd hh (by simp)
    | some cvTa =>
      obtain ⟨ms, -, hms, -, -, -, -, -, -, -, -, -, -, pps, hFD⟩ := hsyn m cvTa hm
      refine ⟨pps, fun cvTa' hh => ?_, fun hh => nomatch hh⟩
      obtain rfl := Option.some.inj hh
      rw [show (p₀.toBlockShape.withSort s0).nIdxs.getD m 0 = ms.nIdx from hnIdxAt m ms hms]
      exact hFD.congr_sort (hsEval m)
  refine ⟨fun m => Classical.choose (hfdEx m), sOf, ?_⟩
  have hfd : ∀ (m : Nat) (cvTa : ConstantVal), cvTas[m]? = some cvTa →
      FormerData mp.base2 cvTa
        ((p₀.toBlockShape.withSort s0).nP + (p₀.toBlockShape.withSort s0).nIdxs.getD m 0)
        (p₀.toBlockShape.withSort s0).resSort (Classical.choose (hfdEx m)) :=
    fun m cvTa hm => (Classical.choose_spec (hfdEx m)).1 cvTa hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsEval, hfd,
    fun m hm => (Classical.choose_spec (hfdEx m)).2 hm, ?_⟩
  · -- one former per member
    show cvTas.length = (p₀.toBlockShape.withSort s0).members.length
    rw [hcvTas, hmembers]
    simp only [List.length_cons, List.length_map]
    rw [hlenCvs]
  · intro m cvTa hm
    obtain ⟨ms, -, hms, hn, -⟩ := hsyn m cvTa hm
    rw [hn, hnameAt m ms hms]
  · intro m cvTa hm
    obtain ⟨ms, -, hms, -, hl, -⟩ := hsyn m cvTa hm
    rw [hl]
    exact hlps ms (by rw [← hmembers] at *; exact List.mem_of_getElem? hms)
  · intro m cvTa hm
    obtain ⟨-, -, -, -, -, hfind, -⟩ := hsyn m cvTa hm
    exact hfind
  · intro m cvTa hm
    obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := hsyn m cvTa hm
    exact htr
  · intro m cvTa hm
    obtain ⟨-, -, -, -, -, -, hnres, -⟩ := hsyn m cvTa hm
    exact hnres
  · intro m cvTa hm
    obtain ⟨-, -, -, -, -, -, -, hpsh, -⟩ := hsyn m cvTa hm
    exact hpsh
  · intro m cvTa hm
    obtain ⟨-, -, -, -, -, -, -, -, -, htf, hlpd, hbt, -⟩ := hsyn m cvTa hm
    exact ⟨htf, hlpd, hbt⟩
  · intro m cvTa hm
    obtain ⟨ms, bs, hms, -, -, -, -, -, -, -, -, -, hst, -⟩ := hsyn m cvTa hm
    exact ⟨bs, by rw [show (p₀.toBlockShape.withSort s0).nIdxs.getD m 0 = ms.nIdx from
      hnIdxAt m ms hms]; exact hst⟩
  · -- official's parameter agreement, semantically
    have := blockParamsIff hμ mp h
      (nPOf := fun m => (p₀.toBlockShape.withSort s0).nP
        + (p₀.toBlockShape.withSort s0).nIdxs.getD m 0)
      (fun _ => Nat.le_add_right _ _) hfd
    intro m₁ m₂ h₁ h₂ ψ ρ
    refine this m₁ m₂ ?_ ?_ ψ ρ
    · rw [show cvTas.length = (p₀.toBlockShape.withSort s0).members.length from by
        rw [hcvTas, hmembers]; simp only [List.length_cons, List.length_map]; rw [hlenCvs]]
      exact h₁
    · rw [show cvTas.length = (p₀.toBlockShape.withSort s0).members.length from by
        rw [hcvTas, hmembers]; simp only [List.length_cons, List.length_map]; rw [hlenCvs]]
      exact h₂

/-! ## One former pass -/

/-- Distinct positions of a duplicate-free list carry distinct
entries. -/
theorem nodup_getElem_ne : ∀ {α : Type} {L : List α}, L.Nodup →
    ∀ {i j : Nat} (hi : i < L.length) (hj : j < L.length), i ≠ j → L[i] ≠ L[j]
  | _, [], _, i, _, hi, _, _ => absurd hi (by simp)
  | _, a :: L, h, i, j, hi, hj, hne => by
    rcases i with _ | i <;> rcases j with _ | j
    · exact absurd rfl hne
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      intro hh
      exact (List.nodup_cons.mp h).1 (hh ▸ List.getElem_mem (by simpa using hj))
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      intro hh
      exact (List.nodup_cons.mp h).1 (hh ▸ List.getElem_mem (by simpa using hi))
    · simp only [List.getElem_cons_succ]
      exact nodup_getElem_ne (List.nodup_cons.mp h).2 (by simpa using hi) (by simpa using hj)
        (fun hh => hne (by omega))

/-- **One former pass**: the `k` formers consed in block order with
the leaves `A`, at the capability records the block owes.  BOTH passes
of the assembly are this theorem — the DUMMY one at the empty chains,
at whose carrier the constructors are read, and the REAL one at the
fixpoint leaves those readings build.  The η invariant is threaded
over the whole member list, because all `k` formers are stored before
any constructor is. -/
theorem blockFormerPass (mp : EnvModelM V μ env) {F : Nat} {p₀ : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {q : BlockShape} {envI : Env}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {sOf : Nat → Level}
    (hInd : ConLeche.checkBlockInds (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p₀ isRec
      = .ok (envI, cvTas, q))
    (hF : BlockFormerFacts mp q cvTas ppsOf sOf)
    (hnd : q.memberNames.Nodup)
    (hE : ConLeche.EtaFamiliesClosed env)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (hAbelowOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A j ψ).erase)
    (hAparamsOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      ∀ ψ₁ ψ₂ : Name → Nat, (∀ n ∈ cvTa.levelParams, ψ₁ n = ψ₂ n) → A j ψ₁ = A j ψ₂)
    (hAokOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A j ψ))
    (hAvalidOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotValid V ρ (A j ψ))
    (hAmemOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (A j ψ) ∈ˢ interp V ρ (mkPisAV (ppsOf j ψ) (.sort (q.resSort.eval ψ))))
    (hetaNe : ∀ (j j' : Nat) (cvTa cvTb : ConstantVal), cvTas[j]? = some cvTa →
      cvTas[j']? = some cvTb → (ConLeche.blockCapsAt q j isRec).eta = true →
      cvTb.name ≠ (ConLeche.blockCapsAt q j isRec).etaCtor)
    (hetaFresh : ∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
      (ConLeche.blockCapsAt q j isRec).eta = true →
      env.find? (ConLeche.blockCapsAt q j isRec).etaCtor = none)
    (hTlawsOf : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      ∀ {env' : Env} (m' : EnvModel V env'),
      FormerData m' cvTa (q.nP + q.nIdxs.getD j 0) q.resSort (ppsOf j) →
      env'.find? cvTa.name = none → ConstsBound env' cvTa.type →
      (∀ (j' : Nat) (cvTb : ConstantVal), cvTas[j']? = some cvTb →
        (ConLeche.blockCapsAt q j' isRec).eta = true →
        env'.find? (ConLeche.blockCapsAt q j' isRec).etaCtor = none) →
      ∀ m₂ : EnvModel V ⟨.indInfo cvTa (ConLeche.blockCapsAt q j isRec) :: env'.consts⟩,
      m₂.acval = acvalWith m'.acval cvTa.name (A j) →
      CapsLawsAt m₂ cvTa.name cvTa (ConLeche.blockCapsAt q j isRec)) :
    ∃ mp' : EnvModelM V μ envI,
      ConLeche.EtaFamiliesClosedExceptL envI q.memberNames ∧
      (∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
        FormerData mp'.base2 cvTa (q.nP + q.nIdxs.getD j 0) q.resSort (ppsOf j)) ∧
      (∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
        envI.find? cvTa.name = some (.indInfo cvTa (ConLeche.blockCapsAt q j isRec)) ∧
        ∀ ψ, mp'.base2.acval cvTa.name ψ = A j ψ) ∧
      (∀ n : Name, (∀ cvTb ∈ cvTas, n ≠ cvTb.name) →
        mp'.base2.acval n = mp.base2.acval n) := by
  obtain ⟨-, -, -, -, -, -, -, -, rfl, -, -, -⟩ := ConLeche.checkBlockInds_shape hInd
  have hlenNames : q.memberNames.length = cvTas.length := by
    rw [hF.lenCv]
    show (q.members.map (·.cvT.name)).length = q.members.length
    simp
  have hnameG : ∀ (j : Nat) (cvTa : ConstantVal) (hj : j < q.memberNames.length),
      cvTas[j]? = some cvTa → cvTa.name = q.memberNames[j] := by
    intro j cvTa hj hjq
    rw [hF.nameOf j cvTa hjq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  exact stageBlockFormers (V := V) (μ := μ) (p₁ := q) (isRec := isRec)
    (names := q.memberNames) (cvTasAll := cvTas) (A := A)
    (nPOf := fun j => q.nP + q.nIdxs.getD j 0) (resSort := q.resSort) (ppsOf := ppsOf)
    (fun j cvTa hj => by
      have hjl : j < q.memberNames.length := by
        rw [hlenNames]; exact (List.getElem?_eq_some_iff.mp hj).1
      rw [hnameG j cvTa hjl hj]
      exact List.getElem_mem hjl)
    (fun j j' c c' hj hj' hjj => by
      have hjl : j < q.memberNames.length := by
        rw [hlenNames]; exact (List.getElem?_eq_some_iff.mp hj).1
      have hjl' : j' < q.memberNames.length := by
        rw [hlenNames]; exact (List.getElem?_eq_some_iff.mp hj').1
      rw [hnameG j c hjl hj, hnameG j' c' hjl' hj']
      exact nodup_getElem_ne hnd hjl hjl' hjj)
    hF.nresOf hF.pshapeOf
    (fun j cvTa hj => by
      obtain ⟨htf, hlpd, hbt⟩ := hF.tyWFOf j cvTa hj
      obtain ⟨bs, hst⟩ := hF.stripOf j cvTa hj
      exact ⟨htf, hlpd, hbt,
        ConLeche.stripPis_isSome_of_le (Nat.le_add_right _ _) (by rw [hst]; rfl)⟩)
    hAbelowOf hAparamsOf hAokOf hAvalidOf hAmemOf hetaNe hTlawsOf
    cvTas 0 env mp (fun j => by rw [Nat.zero_add]) (Nat.zero_add _)
    (hE.exceptL q.memberNames) hF.resolveOf (fun j cvTa _ hj => hF.freshOf j cvTa hj)
    hetaFresh hF.fdOf
    (fun j cvTa hj _ => absurd hj (Nat.not_lt_zero _))

/-! ## A structure-like member's projection family is free -/

/-- A name absent from a cons is absent from the base. -/
theorem find?_none_of_consB {c : ConstantInfo} {env : Env} {n : Name}
    (h : Env.find? ⟨c :: env.consts⟩ n = none) : env.find? n = none := by
  rw [ConLeche.Env.find?_cons] at h
  split at h
  · exact nomatch h
  · exact h

/-- **A structure-like member's projection-FUNCTION family is free at
the pre-table environment.**  The member's own table check requires
its `nF` projection names fresh where it runs, and every environment
the tables' loop threads is a cons over the previous one — so the
family is free already where the loop started, and (by the install's
other conses) below it.  This is `fixTableFamFree` at `k` members. -/
theorem blockTablesFamFree {q : BlockShape} :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level)))
      (env env₂ : Env),
      ConLeche.checkBlockTables (m := ConLeche.CheckM) q l env = .ok env₂ →
      ∀ (i : Nat) (e : MemberShape × List (ConstantVal × Nat) × List (List Level)),
        l[i]? = some e → ∀ (cA : ConstantVal × Nat) (sorts : List Level),
        e.2.1 = [cA] → e.2.2 = [sorts] → e.1.nIdx = 0 → 0 < cA.2 →
        env.find? (projFnName e.1.cvT.name 0) = none
  | [], _, _, _, _, _, hi, _, _, _, _, _, _ => by simp at hi
  | (ms, ctorsA, sortss) :: rest, env, env₂, h, i, e, hi, cA, sorts, hc, hs, hidx, hpos => by
    have hkey : ∃ env' : Env,
        ConLeche.checkBlockTables (m := ConLeche.CheckM) q rest env' = .ok env₂ ∧
        (∀ n : Name, env'.find? n = none → env.find? n = none) ∧
        (∀ (cB : ConstantVal × Nat) (sortsB : List Level),
          ctorsA = [cB] → sortss = [sortsB] → ms.nIdx = 0 → 0 < cB.2 →
          env.find? (projFnName ms.cvT.name 0) = none) := by
      cases ctorsA with
      | nil =>
        refine ⟨env, ?_, fun _ hh => hh, fun _ _ hcc _ _ _ => by simp at hcc⟩
        rw [ConLeche.checkBlockTables] at h
        · exact h
        · simp
      | cons cA0 ctl =>
      cases ctl with
      | cons c2 ctl2 =>
        refine ⟨env, ?_, fun _ hh => hh, fun _ _ hcc _ _ _ => by simp at hcc⟩
        rw [ConLeche.checkBlockTables] at h
        · exact h
        · simp
      | nil =>
      cases sortss with
      | nil =>
        refine ⟨env, ?_, fun _ hh => hh, fun _ _ _ hss _ _ => by simp at hss⟩
        rw [ConLeche.checkBlockTables] at h
        · exact h
        · simp
      | cons s0 stl =>
      cases stl with
      | cons s2 stl2 =>
        refine ⟨env, ?_, fun _ hh => hh, fun _ _ _ hss _ _ => by simp at hss⟩
        rw [ConLeche.checkBlockTables] at h
        · exact h
        · simp
      | nil =>
      rw [ConLeche.checkBlockTables] at h
      by_cases hidx0 : (ms.nIdx == 0) = true
      case neg =>
        rw [if_neg hidx0] at h
        exact ⟨env, h, fun _ hh => hh, fun _ _ _ _ hii _ =>
          absurd (by rw [hii]; rfl) hidx0⟩
      rw [if_pos hidx0] at h
      cases hT : ConLeche.checkStructProjTable (m := ConLeche.CheckM) ms.cvT.name cA0.1.name
          q.lps q.nP cA0.2 q.resSort (ConLeche.structProjGuards cA0.1.type q.nP cA0.2 s0)
          1 cA0.1 env with
      | error er => rw [hT] at h; exact nomatch h
      | ok env' =>
        rw [hT] at h
        have hinv := ConLeche.checkStructProjTable_inv hT
        obtain ⟨_bodies, _hb1, _hb2, hfree, _hb4, henvOut⟩ := hinv
        refine ⟨env', h, fun n hn => ?_, fun cB sortsB hcc _ _ hposB => ?_⟩
        · rw [henvOut] at hn
          exact find?_none_of_consB hn
        · obtain rfl : cB = cA0 := by simpa using hcc.symm
          exact Option.isNone_iff_eq_none.mp
            (List.all_eq_true.mp hfree 0 (List.mem_range.mpr hposB))
    obtain ⟨env', hrest, hmono, hhere⟩ := hkey
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact hhere cA sorts hc hs hidx hpos
    | succ j =>
      simp only [List.getElem?_cons_succ] at hi
      exact hmono _ (blockTablesFamFree rest env' env₂ hrest j e hi cA sorts hc hs hidx hpos)

/-- **A structure-like member's projection TABLE name is free at the
pre-table environment** — the `projTableName` twin of
`blockTablesFamFree`, and by the same argument: the member's own table
check requires the name fresh where it runs, and every environment the
tables' loop threads is a cons over the previous one.

It is what carries `annotateCore`'s projection-slot guarantee to the
block's OWN members: a constructor type annotated at the formers'
environment carries a `.proj T i` node only where a table for `T` was
stored THERE, and none of the block's members has one. -/
theorem blockTablesTblFree {q : BlockShape} :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level)))
      (env env₂ : Env),
      ConLeche.checkBlockTables (m := ConLeche.CheckM) q l env = .ok env₂ →
      ∀ (i : Nat) (e : MemberShape × List (ConstantVal × Nat) × List (List Level)),
        l[i]? = some e → ∀ (cA : ConstantVal × Nat) (sorts : List Level),
        e.2.1 = [cA] → e.2.2 = [sorts] → e.1.nIdx = 0 →
        env.find? (projTableName e.1.cvT.name) = none
  | [], _, _, _, _, _, hi, _, _, _, _, _ => by simp at hi
  | (ms, ctorsA, sortss) :: rest, env, env₂, h, i, e, hi, cA, sorts, hc, hs, hidx => by
    have hkey : ∃ env' : Env,
        ConLeche.checkBlockTables (m := ConLeche.CheckM) q rest env' = .ok env₂ ∧
        (∀ n : Name, env'.find? n = none → env.find? n = none) ∧
        (∀ (cB : ConstantVal × Nat) (sortsB : List Level),
          ctorsA = [cB] → sortss = [sortsB] → ms.nIdx = 0 →
          env.find? (projTableName ms.cvT.name) = none) := by
      cases ctorsA with
      | nil =>
        refine ⟨env, ?_, fun _ hh => hh, fun _ _ hcc _ _ => by simp at hcc⟩
        rw [ConLeche.checkBlockTables] at h
        · exact h
        · simp
      | cons cA0 ctl =>
      cases ctl with
      | cons c2 ctl2 =>
        refine ⟨env, ?_, fun _ hh => hh, fun _ _ hcc _ _ => by simp at hcc⟩
        rw [ConLeche.checkBlockTables] at h
        · exact h
        · simp
      | nil =>
      cases sortss with
      | nil =>
        refine ⟨env, ?_, fun _ hh => hh, fun _ _ _ hss _ => by simp at hss⟩
        rw [ConLeche.checkBlockTables] at h
        · exact h
        · simp
      | cons s0 stl =>
      cases stl with
      | cons s2 stl2 =>
        refine ⟨env, ?_, fun _ hh => hh, fun _ _ _ hss _ => by simp at hss⟩
        rw [ConLeche.checkBlockTables] at h
        · exact h
        · simp
      | nil =>
      rw [ConLeche.checkBlockTables] at h
      by_cases hidx0 : (ms.nIdx == 0) = true
      case neg =>
        rw [if_neg hidx0] at h
        exact ⟨env, h, fun _ hh => hh, fun _ _ _ _ hii => absurd (by rw [hii]; rfl) hidx0⟩
      rw [if_pos hidx0] at h
      cases hT : ConLeche.checkStructProjTable (m := ConLeche.CheckM) ms.cvT.name cA0.1.name
          q.lps q.nP cA0.2 q.resSort (ConLeche.structProjGuards cA0.1.type q.nP cA0.2 s0)
          1 cA0.1 env with
      | error er => rw [hT] at h; exact nomatch h
      | ok env' =>
        rw [hT] at h
        obtain ⟨_bodies, _hb1, _hb2, _hb3, hfreshT, henvOut⟩ :=
          ConLeche.checkStructProjTable_inv hT
        refine ⟨env', h, fun n hn => ?_, fun _ _ _ _ _ => hfreshT⟩
        rw [henvOut] at hn
        exact find?_none_of_consB hn
    obtain ⟨env', hrest, hmono, hhere⟩ := hkey
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact hhere cA sorts hc hs hidx
    | succ j =>
      simp only [List.getElem?_cons_succ] at hi
      exact hmono _ (blockTablesTblFree rest env' env₂ hrest j e hi cA sorts hc hs hidx)

/-! ## The dummy pass -/

/-- A member's index count, read off the record two ways. -/
theorem blockNIdxs_getD {q : BlockShape} {j : Nat} (hj : j < q.members.length) :
    q.nIdxs.getD j 0 = (q.members.getD j default).nIdx := by
  show (q.members.map (·.nIdx)).getD j 0 = (q.members.getD j default).nIdx
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- A unit-like member has no index. -/
theorem blockCapsAt_unitlike_nIdx {q : BlockShape} {j : Nat} {isRec : Bool}
    (hu : (ConLeche.blockCapsAt q j isRec).unitlike = true) :
    (q.members.getD j default).nIdx = 0 := by
  rcases blockCapsAt_cases q j isRec with ⟨c, -, hc⟩ | hc
  · rw [hc] at hu
    simp only [Bool.and_eq_true, beq_iff_eq] at hu
    exact hu.1
  · rw [hc] at hu; exact nomatch hu

/-- **The DUMMY former pass**: the `k` formers consed with the EMPTY
chain lists — `declNative`'s `stageSumFormer` at `k` members.  This is
the carrier at which the members' constructors' readings are taken:
every member's leaf must exist before any real one is built, because a
member's fixpoint leaf mentions every member's chains. -/
theorem blockDummyPass (mp : EnvModelM V μ env) {F : Nat} {p₀ : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {q : BlockShape} {envI : Env}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {sOf : Nat → Level}
    (hInd : ConLeche.checkBlockInds (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p₀ isRec
      = .ok (envI, cvTas, q))
    (hF : BlockFormerFacts mp q cvTas ppsOf sOf)
    (hnd : q.memberNames.Nodup)
    (hE : ConLeche.EtaFamiliesClosed env)
    (hetaNe : ∀ (j j' : Nat) (cvTa cvTb : ConstantVal), cvTas[j]? = some cvTa →
      cvTas[j']? = some cvTb → (ConLeche.blockCapsAt q j isRec).eta = true →
      cvTb.name ≠ (ConLeche.blockCapsAt q j isRec).etaCtor)
    (hetaFresh : ∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
      (ConLeche.blockCapsAt q j isRec).eta = true →
      env.find? (ConLeche.blockCapsAt q j isRec).etaCtor = none) :
    ∃ mp' : EnvModelM V μ envI,
      ConLeche.EtaFamiliesClosedExceptL envI q.memberNames ∧
      (∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
        FormerData mp'.base2 cvTa (q.nP + q.nIdxs.getD j 0) q.resSort (ppsOf j)) ∧
      (∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
        envI.find? cvTa.name = some (.indInfo cvTa (ConLeche.blockCapsAt q j isRec)) ∧
        ∀ ψ, mp'.base2.acval cvTa.name ψ
          = sumTyAV (q.resSort.eval ψ) (ppsOf j ψ) []) ∧
      (∀ n : Name, (∀ cvTb ∈ cvTas, n ≠ cvTb.name) →
        mp'.base2.acval n = mp.base2.acval n) := by
  -- the leaf's currency at EVERY position: on the block from the
  -- member's telescope reading, off it at the empty telescope
  have hwalks : ∀ (j : Nat) (ψ : Name → Nat) (ρ : Nat → V),
      ParamsOkS (q.resSort.eval ψ) ρ [] (ppsOf j ψ) ∧
        UnderTowerValid ρ (sumBodyAV (q.resSort.eval ψ) []) (ppsOf j ψ) := by
    intro j ψ ρ
    have htriv : ∀ (w : Nat) (σ : Nat → V),
        SumFieldsOkB (V := V) w σ [] ∧ SumFieldsValid (V := V) σ [] := by
      intro w σ
      constructor
      · intro Fs hFs; exact nomatch hFs
      · intro Fs hFs; exact nomatch hFs
    cases hj : cvTas[j]? with
    | none =>
      rw [hF.ppsNil j hj ψ]
      refine ⟨?_, ?_⟩
      · show SumFieldsOkB (q.resSort.eval ψ) ρ []
        exact (htriv _ ρ).1
      · show AnnotValid V ρ (sumBodyAV (q.resSort.eval ψ) [])
        exact sumBodyAV_validV (htriv (q.resSort.eval ψ) ρ).2
    | some cvTa =>
      exact formerWalksS (hF.fdOf j cvTa hj) (fun ψ' ρ' _ => htriv _ ρ') ψ ρ
  have hbelow : ∀ (j : Nat) (ψ : Name → Nat), DomsBelow 0 (ppsOf j ψ) := by
    intro j ψ
    cases hj : cvTas[j]? with
    | none => rw [hF.ppsNil j hj ψ]; trivial
    | some cvTa => exact (hF.fdOf j cvTa hj).below ψ
  refine blockFormerPass mp hInd hF hnd hE
    (fun j ψ => sumTyAV (q.resSort.eval ψ) (ppsOf j ψ) [])
    (fun j _ _ ψ => sumTyAV_below (hbelow j ψ) (by intro Fs hFs; exact nomatch hFs))
    (fun j cvTa hj ψ₁ ψ₂ hφ => by
      obtain ⟨hp, hw⟩ := (hF.fdOf j cvTa hj).params ψ₁ ψ₂ hφ
      show sumTyAV _ _ [] = sumTyAV _ _ []
      rw [hp, hw])
    (fun j _ _ ψ ρ => sumTyAV_wellDenoted (hwalks j ψ ρ).1)
    (fun j _ _ ψ ρ => (sumTyAV_wellDenotedV (hwalks j ψ ρ).1 (hwalks j ψ ρ).2).2)
    (fun j _ _ ψ ρ => sumTyAV_mem (hwalks j ψ ρ).1)
    hetaNe hetaFresh ?_
  -- the capability laws at the DUMMY leaf: η is vacuous (no
  -- constructor is stored), unit-likeness folds the empty-chain leaf
  -- to the one tagged empty tuple
  intro j cvTa hj env' m' hFD' hfreshT hcb hfreshC m₂ hac
  have hFD₂ : FormerData m₂ cvTa (q.nP + q.nIdxs.getD j 0) q.resSort (ppsOf j) :=
    hFD'.cross (c₀ := .indInfo cvTa (ConLeche.blockCapsAt q j isRec)) hfreshT
      (ConsCrossAt.ofNtc fun _ hh => nomatch hh) hcb m₂ hac
  have hleaf : ∀ ψ, m₂.acval cvTa.name ψ = sumTyAV (q.resSort.eval ψ) (ppsOf j ψ) [] := by
    intro ψ
    rw [hac]
    exact congrFun acvalWith_self ψ
  refine ⟨fun he hfam => ?_, fun hu φ' => ?_⟩
  · exfalso
    obtain ⟨-, ⟨cvC, cnP, cnF, hfC⟩, -⟩ := hfam
    rw [ConLeche.Env.find?_cons,
      if_neg (fun hh => hetaNe j j cvTa cvTa hj hj he (by
        show cvTa.name = (ConLeche.blockCapsAt q j isRec).etaCtor
        exact hh)),
      hfreshC j cvTa hj he] at hfC
    exact nomatch hfC
  · refine fixEmptyUnitLaw hleaf hFD₂.read hFD₂.okTy (fun ψ => ?_)
    rw [(blockCapsAt_unitlike hu).2.2, hFD₂.len ψ,
      blockNIdxs_getD (q := q) (j := j) (by
        have := (List.getElem?_eq_some_iff.mp hj).1
        rwa [hF.lenCv] at this),
      blockCapsAt_unitlike_nIdx hu, Nat.add_zero]

/-! ## The members' index telescopes -/

/-- Positional reading of a zip. -/
theorem zip_getElem? : ∀ {α β : Type} (l₁ : List α) (l₂ : List β) (i : Nat) (a : α) (b : β),
    l₁[i]? = some a → l₂[i]? = some b → (l₁.zip l₂)[i]? = some (a, b)
  | _, _, [], _, _, _, _, h, _ => by simp at h
  | _, _, _ :: _, [], _, _, _, _, h => by simp at h
  | _, _, _ :: _, _ :: _, 0, a, b, h₁, h₂ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
    subst h₁; subst h₂; rfl
  | _, _, x :: l₁, y :: l₂, i + 1, a, b, h₁, h₂ => by
    simp only [List.getElem?_cons_succ] at h₁ h₂
    show (List.zip (x :: l₁) (y :: l₂))[i + 1]? = _
    rw [List.zip_cons_cons]
    simp only [List.getElem?_cons_succ]
    exact zip_getElem? l₁ l₂ i a b h₁ h₂

/-- **Every member's index telescope is graded and valid** at its own
parameter frame, at the universe its index binders' sorts give
(`idxOk_of`/`idxValid_of` at `k` members, from conjunct 6). -/
theorem blockIdxFacts_of (hμ : μ.verifiedChecks = true) {F : Nat} {envI : Env}
    (mpI : EnvModelM V μ envI) {q : BlockShape} {cvTas : List ConstantVal}
    {isorts : List (List Level)} {isRec : Bool}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hsorts : ConLeche.checkBlockIdxSorts (ConLeche.fueledOps μ F) envI q
      (q.members.zip cvTas) = .ok isorts)
    (hlenCv : cvTas.length = q.k)
    (hfind : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      envI.find? cvTa.name = some (.indInfo cvTa (ConLeche.blockCapsAt q j isRec)))
    (hFD : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      FormerData mpI.base2 cvTa (q.nP + q.nIdxs.getD j 0) q.resSort (ppsOf j))
    (hlps : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      cvTa.levelParams = q.lps) :
    ∃ uOf : Nat → (Name → Nat) → Nat,
      (∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
        ∀ (ψ : Name → Nat) (ρp : Nat → V),
        Sat V (((ppsOf j ψ).take q.nP).map (·.2.2)).reverse ρp →
        IdxOk (uOf j ψ) ρp (((ppsOf j ψ).drop q.nP).map (·.2.2)) ∧
        FieldsValid ρp (((ppsOf j ψ).drop q.nP).map (·.2.2))) ∧
      ∀ (j : Nat) (ψ₁ ψ₂ : Name → Nat), (∀ n ∈ q.lps, ψ₁ n = ψ₂ n) →
        uOf j ψ₁ = uOf j ψ₂ := by
  obtain ⟨-, hall⟩ := ConLeche.checkBlockIdxSorts_inv hsorts
  refine ⟨fun j ψ => idxUniv (restrictΨ q.lps ψ) (isorts.getD j []), ?_, ?_⟩
  · intro j cvTa hj ψ ρp hρp
    have hjk : j < q.members.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      rw [hlenCv] at this
      exact this
    obtain ⟨ms, hms⟩ : ∃ ms, q.members[j]? = some ms := ⟨_, List.getElem?_eq_getElem hjk⟩
    obtain ⟨is, tfvs, trest, hisj, hop, hsortsj⟩ :=
      hall j (ms, cvTa) (zip_getElem? _ _ _ _ _ hms hj)
    have hnIdx : q.nIdxs.getD j 0 = ms.nIdx := by
      rw [blockNIdxs_getD hjk, List.getD_eq_getElem?_getD, hms]; rfl
    have hisD : isorts.getD j [] = is := by
      rw [List.getD_eq_getElem?_getD, hisj]; rfl
    have hFDj : FormerData mpI.base2 cvTa (q.nP + ms.nIdx) q.resSort (ppsOf j) := by
      rw [← hnIdx]; exact hFD j cvTa hj
    have hppsR : ppsOf j (restrictΨ q.lps ψ) = ppsOf j ψ :=
      (hFDj.params _ _ fun n hn =>
        restrictΨ_agree _ _ n (by rw [← hlps j cvTa hj]; exact hn)).1
    refine ⟨?_, idxValid_of mpI (hfind j cvTa hj) hop hFDj ψ ρp hρp⟩
    have hok := idxOk_of hμ mpI (hfind j cvTa hj) hop hsortsj hFDj
      (restrictΨ q.lps ψ) ρp (by rw [hppsR]; exact hρp)
    rw [hppsR] at hok
    show IdxOk (idxUniv (restrictΨ q.lps ψ) (isorts.getD j [])) ρp _
    rw [hisD]
    exact hok
  · intro j ψ₁ ψ₂ hφ
    show idxUniv (restrictΨ q.lps ψ₁) _ = idxUniv (restrictΨ q.lps ψ₂) _
    rw [restrictΨ_congr hφ]

/-! ## The constructors' readings at one member -/

/-- A block constructor's data functions at ONE member, bundled for
the choice. -/
structure BlockMemberPick where
  idxF : Nat → List Expr
  dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)
  esF : Nat → (Name → Nat) → List AnnotTerm
  srcsF : Nat → List (Option Nat)
  fvsPF : Nat → List Expr
  xFvsF : Nat → List Expr
  xrestF : Nat → Expr
  /-- the fields with holes (`BlockData.absFF`): not a reading of this
  member's run — the block's datum chooses them once, at the dummy
  carrier, and every pick of the block carries the same -/
  absF : Nat → (Name → Nat) → List AnnotTerm
  /-- the positivity walk's normal forms (`BlockData.nfFF`), shared like `absF` -/
  nf : Nat → Expr

/-- **The constructors' data functions at ONE member of a block**,
stated the way `BlockData` reads them: `blockCtorFuns_of` at member
`m`. -/
theorem blockCtorFunsAt (hμ : μ.verifiedChecks = true) {F : Nat}
    {envI : Env} (mpI : EnvModelM V μ envI) {q : BlockShape} {cvTas : List ConstantVal}
    {isRec : Bool} {m : Nat} {cvTa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {sOf : Nat → Level}
    (hm : cvTas[m]? = some cvTa)
    (hnameOf : ∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
      cvTb.name = q.memberNames.getD j .anonymous)
    (hlpsOf : ∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
      cvTb.levelParams = q.lps)
    (hsEval : ∀ (j : Nat) (ψ : Name → Nat), (sOf j).eval ψ = q.resSort.eval ψ)
    (hstripOf : ∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
      ∃ bs : List (Expr × BinderMeta),
        cvTb.type.stripPis (q.nP + q.nIdxs.getD j 0) = some (bs, .sort (sOf j)))
    (hfindOf : ∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
      envI.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt q j isRec)))
    (hrunOf : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ (c : ConstantVal × Nat) (sorts : List Level),
        ConLeche.checkSumCtor (ConLeche.fueledOps μ F) envI envI cvTa.name q.lps q.nP
          (q.nIdxs.getD m 0) q.resSort q.isProp q.large c.1 cA.2 cvTa = .ok (cA.1, sorts)) :
    ∃ pk : BlockMemberPick,
      ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
        BlockCtorDataI mpI.base2 (q.memberNames.getD m .anonymous)
          q.lps cA.1 q.nP cA.2 (q.nIdxs.getD m 0) q.resSort q.isProp q.large
          (pk.idxF j) (pk.dsF j) (pk.esF j) (pk.srcsF j)
          (pk.fvsPF j) (pk.xFvsF j) (pk.xrestF j) := by
  obtain ⟨bs, hst⟩ := hstripOf m cvTa hm
  obtain ⟨idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF, hall⟩ :=
    blockCtorFuns_of (V := V) hμ mpI (T := cvTa.name) (lps := q.lps) (nP := q.nP)
      (nIdx := q.nIdxs.getD m 0) (resSort := q.resSort) (isProp := q.isProp) (large := q.large)
      (cvTa := cvTa) (env₁ := envI) (sT := sOf m)
      (hfindOf m cvTa hm) (hlpsOf m cvTa hm) (hsEval m) hst hrunOf
  refine ⟨⟨idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF, fun _ _ => [], fun _ => .bvar 0⟩, fun j cA hj => ?_⟩
  rw [← hnameOf m cvTa hm]
  exact hall j cA hj

/-! ## The real pass -/

/-- **The REAL former pass**: the `k` formers consed with the FIXPOINT
leaves the dummy pass's readings build — `declNative`'s
`stageFixFormer` at `k` members.  The block operator's premise bundle
at the LEAF's chains (`hIdxAll`, `hXAll`, `hXVAll`) is what
`blockLeafWalks` turns into the leaf's two hereditary premises, and
the `blockTyAV` capstones into its five currency facts.  A unit-like
member's law comes through its leaf's FOLD alone (`hfoldZ`), which is
a statement about the leaf TERM and therefore crosses every cons. -/
theorem blockRealPass (mp : EnvModelM V μ env) {F : Nat} {p₀ : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {q : BlockShape} {envI : Env}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {sOf : Nat → Level}
    {uOf : Nat → (Name → Nat) → Nat} {Chs : (Name → Nat) → Nat → List (List AnnotTerm)}
    (hInd : ConLeche.checkBlockInds (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p₀ isRec
      = .ok (envI, cvTas, q))
    (hF : BlockFormerFacts mp q cvTas ppsOf sOf)
    (hnd : q.memberNames.Nodup)
    (hE : ConLeche.EtaFamiliesClosed env)
    (hetaNe : ∀ (j j' : Nat) (cvTa cvTb : ConstantVal), cvTas[j]? = some cvTa →
      cvTas[j']? = some cvTb → (ConLeche.blockCapsAt q j isRec).eta = true →
      cvTb.name ≠ (ConLeche.blockCapsAt q j isRec).etaCtor)
    (hetaFresh : ∀ (j : Nat) (cvTb : ConstantVal), cvTas[j]? = some cvTb →
      (ConLeche.blockCapsAt q j isRec).eta = true →
      env.find? (ConLeche.blockCapsAt q j isRec).etaCtor = none)
    -- the index telescopes' lengths, bounds and the chains' bounds
    (hIdsLen : ∀ (j : Nat) (ψ : Name → Nat),
      (((ppsOf j ψ).drop q.nP).map (·.2.2)).length = q.nIdxs.getD j 0)
    (hIdsBelow : ∀ (c : Nat) (ψ : Name → Nat),
      FieldsBelow q.nP (((ppsOf c ψ).drop q.nP).map (·.2.2)))
    (hchainsBelow : ∀ (ψ : Name → Nat) (c : Nat), c < q.k →
      ∀ chain ∈ Chs ψ c, FieldsBelow (q.nP + 2) chain)
    -- the leaf's data depends on the block's level parameters only
    (hZparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ n ∈ q.lps, ψ₁ n = ψ₂ n) →
      (∀ c, uOf c ψ₁ = uOf c ψ₂) ∧ Chs ψ₁ = Chs ψ₂)
    -- the block operator's premise bundle, at every MEMBER's frame
    -- (D-M41: off the block a position has no parameter telescope, so
    -- its `Sat` says nothing and the bundle is not a fact there)
    (hIdxAll : ∀ (j : Nat), j < q.k → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsOf j ψ).take q.nP).map (·.2.2)).reverse ρp →
      BlockIdxOk (V := V) q.k (fun c => uOf c ψ) ρp
        (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) ∧
      ∀ c, c < q.k → FieldsValid ρp (((ppsOf c ψ).drop q.nP).map (·.2.2)))
    (hXAll : ∀ (j : Nat), j < q.k → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsOf j ψ).take q.nP).map (·.2.2)).reverse ρp →
      BlockChainsOkG q.k (q.resSort.eval ψ) ρp (fun c => uOf c ψ)
        (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) (Chs ψ))
    (hXVAll : ∀ (j : Nat), j < q.k → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsOf j ψ).take q.nP).map (·.2.2)).reverse ρp →
      ∀ Y, Y ∈ˢ famsSpaceB q.k (q.resSort.eval ψ) ρp (fun c => uOf c ψ)
        (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) →
      ∀ c, c < q.k → ∀ t, t ∈ˢ idxSet (uOf c ψ) ρp (((ppsOf c ψ).drop q.nP).map (·.2.2)) →
      SumFieldsValid (cons t (cons Y ρp)) (Chs ψ c))
    -- a unit-like member's leaf folds to the one tagged empty tuple
    (hfoldZ : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      (ConLeche.blockCapsAt q j isRec).unitlike = true →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
        SpineFit ρ ((ppsOf j ψ).map (·.2.2)) ts →
        ts.foldl SetTheory.app (interp V ρ
            (blockTyG q.k (q.resSort.eval ψ) (fun c => uOf c ψ)
              (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) (Chs ψ) (ppsOf j ψ) j))
          = sumSet (q.resSort.eval ψ) (sumFibre (q.resSort.eval ψ) (consList ts ρ)
              [[] ++ [idxEqAV []]])) :
    ∃ mp' : EnvModelM V μ envI,
      ConLeche.EtaFamiliesClosedExceptL envI q.memberNames ∧
      (∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
        FormerData mp'.base2 cvTa (q.nP + q.nIdxs.getD j 0) q.resSort (ppsOf j)) ∧
      (∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
        envI.find? cvTa.name = some (.indInfo cvTa (ConLeche.blockCapsAt q j isRec)) ∧
        ∀ ψ, mp'.base2.acval cvTa.name ψ
          = blockTyG q.k (q.resSort.eval ψ) (fun c => uOf c ψ)
              (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) (Chs ψ) (ppsOf j ψ) j) ∧
      (∀ n : Name, (∀ cvTb ∈ cvTas, n ≠ cvTb.name) →
        mp'.base2.acval n = mp.base2.acval n) := by
  -- the members' telescope readings depend on the block's level parameters only
  have hppsParams : ∀ (c : Nat) (ψ₁ ψ₂ : Name → Nat), (∀ n ∈ q.lps, ψ₁ n = ψ₂ n) →
      ppsOf c ψ₁ = ppsOf c ψ₂ := by
    intro c ψ₁ ψ₂ hφ
    cases hc : cvTas[c]? with
    | none => rw [hF.ppsNil c hc, hF.ppsNil c hc]
    | some cvTb =>
      exact ((hF.fdOf c cvTb hc).params ψ₁ ψ₂
        (fun n hn => hφ n (by rw [← hF.lpsOf c cvTb hc]; exact hn))).1
  -- the leaf's two hereditary premises at every member
  have hwalks : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa → j < q.k →
      ∀ ρ : Nat → V, ∀ ψ : Name → Nat,
      ParamsOkG q.k (q.resSort.eval ψ) ρ (fun c => uOf c ψ)
          (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) (Chs ψ) j (ppsOf j ψ) ∧
        UnderTowerValid ρ
          (.app (projAV j ((blockBodyG q.k (q.resSort.eval ψ) (fun c => uOf c ψ)
              (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) (Chs ψ)).liftN
              ((((ppsOf j ψ).drop q.nP).map (·.2.2)).length) 0))
            (mkTowerGo (uOf j ψ) (((ppsOf j ψ).drop q.nP).map (·.2.2)))) (ppsOf j ψ) := by
    intro j cvTa hj hjk ρ ψ
    exact blockLeafWalks (nIdx := q.nIdxs.getD j 0) ((hF.fdOf j cvTa hj).len ψ)
      ((hF.fdOf j cvTa hj).bits ψ)
      (fun ρ' => (hF.fdOf j cvTa hj).okTy ψ ρ') hjk rfl
      (fun ρp hρp => hIdxAll j hjk ψ ρp hρp) (fun ρp hρp => hXAll j hjk ψ ρp hρp)
      (fun ρp hρp => hXVAll j hjk ψ ρp hρp) ρ
  refine blockFormerPass mp hInd hF hnd hE
    (fun j ψ => blockTyG q.k (q.resSort.eval ψ) (fun c => uOf c ψ)
      (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) (Chs ψ) (ppsOf j ψ) j)
    ?_ ?_ ?_ ?_ ?_ hetaNe hetaFresh ?_
  · -- closed
    intro j cvTa hj ψ
    exact blockTyAV_below ((hF.fdOf j cvTa hj).below ψ) ((hF.fdOf j cvTa hj).len ψ)
      (hIdsLen j ψ) (fun c => hIdsBelow c ψ) (fun c hc => hchainsBelow ψ c hc)
  · -- the level parameters
    intro j cvTa hj ψ₁ ψ₂ hφ
    have hφ' : ∀ n ∈ q.lps, ψ₁ n = ψ₂ n :=
      fun n hn => hφ n (by rw [hF.lpsOf j cvTa hj]; exact hn)
    obtain ⟨hu', hch⟩ := hZparams ψ₁ ψ₂ hφ'
    have hw : q.resSort.eval ψ₁ = q.resSort.eval ψ₂ :=
      ((hF.fdOf j cvTa hj).params ψ₁ ψ₂ hφ).2
    show blockTyG _ _ _ _ _ _ _ = blockTyG _ _ _ _ _ _ _
    rw [hw, hch, hppsParams j ψ₁ ψ₂ hφ',
      show (fun c => uOf c ψ₁) = (fun c => uOf c ψ₂) from funext hu',
      show (fun c => ((ppsOf c ψ₁).drop q.nP).map (·.2.2))
        = (fun c => ((ppsOf c ψ₂).drop q.nP).map (·.2.2))
        from funext fun c => by rw [hppsParams c ψ₁ ψ₂ hφ']]
  · -- graded
    intro j cvTa hj ψ ρ
    exact blockTyG_wellDenoted (by
      have := (List.getElem?_eq_some_iff.mp hj).1; rwa [hF.lenCv] at this)
      (hwalks j cvTa hj (by
        have := (List.getElem?_eq_some_iff.mp hj).1; rwa [hF.lenCv] at this) ρ ψ).1
  · -- bit-valid
    intro j cvTa hj ψ ρ
    have hjk : j < q.k := by
      have := (List.getElem?_eq_some_iff.mp hj).1; rwa [hF.lenCv] at this
    exact (blockTyAV_wellDenotedV hjk (hwalks j cvTa hj hjk ρ ψ).1
      (hwalks j cvTa hj hjk ρ ψ).2).2
  · -- the leaf inhabits its type's reading
    intro j cvTa hj ψ ρ
    have hjk : j < q.k := by
      have := (List.getElem?_eq_some_iff.mp hj).1; rwa [hF.lenCv] at this
    exact blockTyG_mem hjk (hwalks j cvTa hj hjk ρ ψ).1
  · -- the capability laws at the FIXPOINT leaf
    intro j cvTa hj env' m' hFD' hfreshT hcb hfreshC m₂ hac
    have hFD₂ : FormerData m₂ cvTa (q.nP + q.nIdxs.getD j 0) q.resSort (ppsOf j) :=
      hFD'.cross (c₀ := .indInfo cvTa (ConLeche.blockCapsAt q j isRec)) hfreshT
        (ConsCrossAt.ofNtc fun _ hh => nomatch hh) hcb m₂ hac
    have hleaf : ∀ ψ, m₂.acval cvTa.name ψ
        = blockTyG q.k (q.resSort.eval ψ) (fun c => uOf c ψ)
            (fun c => ((ppsOf c ψ).drop q.nP).map (·.2.2)) (Chs ψ) (ppsOf j ψ) j := by
      intro ψ
      rw [hac]
      exact congrFun acvalWith_self ψ
    refine ⟨fun he hfam => ?_, fun hu φ' => ?_⟩
    · exfalso
      obtain ⟨-, ⟨cvC, cnP, cnF, hfC⟩, -⟩ := hfam
      rw [ConLeche.Env.find?_cons,
        if_neg (fun hh => hetaNe j j cvTa cvTa hj hj he (by
          show cvTa.name = (ConLeche.blockCapsAt q j isRec).etaCtor
          exact hh)),
        hfreshC j cvTa hj he] at hfC
      exact nomatch hfC
    · refine fibreUnitLaw hleaf (fun ψ ρ ts hsp => hfoldZ j cvTa hj hu ψ ρ ts hsp)
        hFD₂.read hFD₂.okTy (fun ψ => ?_)
      rw [(blockCapsAt_unitlike hu).2.2, hFD₂.len ψ,
        blockNIdxs_getD (q := q) (j := j) (by
          have := (List.getElem?_eq_some_iff.mp hj).1
          rwa [hF.lenCv] at this),
        blockCapsAt_unitlike_nIdx hu, Nat.add_zero]

end ConLeche.Model
