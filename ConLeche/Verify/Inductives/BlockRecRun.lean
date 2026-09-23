module

public import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.ExceptBind

public section

/-!
# The recursor stage's RUN RECORDS

ONE inversion per kernel stage of the recursor check
(`ConLeche/Kernel/Inductives/BlockInstall.lean`), each returning a
record with NAMED fields — the pattern of `DeclBlockRun` for the
install stages.  Every other proof about the recursor stage reads
these records and never unfolds a stage: a new kernel check is a new
field here, proved once, and a one-module edit.

| stage | kernel function | record | inversion |
|---|---|---|---|
| (b)  one recursor's type | `checkBlockRecTys` | `RecTyEntry` | `checkBlockRecTys_run` |
| (b') the family's agreements | `checkBlockRecFamilyAgree` | `RecFamRun` | `checkBlockRecFamilyAgree_run` |
| (c)  one rule | `checkBlockRule` | `RuleRun` | `checkBlockRule_run` |
| (c)  one recursor's rules | `checkBlockRules` | `RulesRun` | `checkBlockRules_run` |
| (c)  every recursor's rules | `checkBlockRecsRules` | `RecRulesEntry` | `checkBlockRecsRules_run` |
| the whole check | `checkBlockRecK` | `RecKRun` | `checkBlockRecK_run` |

`RecKRun` carries the one bridge every consumer needs and used to
re-prove: the recursor constants the stage STORES (`rs[i].1`) are the
ones stage (b) CHECKED (`cvRus[i].1`) — `RecKRun.stored`.  Its
accessors `RecKRun.tyAt`, `RecKRun.rulesAt` and `RecKRun.ruleAt` hand
out the per-recursor and per-rule records at the STORED data.

The records are `Type`-valued (they carry the stage's intermediate
values as data), so an inversion concludes `Nonempty _`, and a
consumer writes `obtain ⟨R⟩ := checkBlockRecK_run h`.
-/

namespace ConLeche

variable {mode : CheckMode}

local syntax "close_throw" term : tactic
local macro_rules
  | `(tactic| close_throw $h:term) =>
    `(tactic| first
        | exact nomatch $h
        | exact absurd $h (by
            simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            exact fun hh => nomatch hh)
        | exact absurd $h
            (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-! ## Stage (b): one recursor's TYPE -/

/-- **Stage (b) at ONE recursor**, every bind of `checkBlockRecTys`'s
body named.  `ri` is the recursor's position in the block, `rc` its
record, and `(cvRi, nIdx, u)` the entry the stage returns for it: the
CHECKED constant, the member's index count and the conclusion's
sort. -/
structure RecTyEntry (mode : CheckMode) (F : Nat) (env : Env) (p : BlockShape)
    (nested : Bool) (cvTas : List ConstantVal) (ri : Nat) (rc : RecShape)
    (cvRi : ConstantVal) (nIdx : Nat) (u : Level) : Type where
  /-- the member the recursor's major names -/
  ms : MemberShape
  /-- that member's checked type former -/
  cvTa : ConstantVal
  /-- the recursor type's `mI + 1` openers and its conclusion -/
  fvs : List Expr
  concl : Expr
  /-- the former's `nP` parameter openers and the rest of its type -/
  tfvs : List Expr
  trest : Expr
  /-- the MAJOR's opener -/
  maj : Expr
  /-- the conclusion's inferred type -/
  sty : Expr
  hms : p.members[p.recTgtAt ri]? = some ms
  hcvTa : cvTas[p.recTgtAt ri]? = some cvTa
  hcv : checkConstantVal (fueledOps mode F) env rc.cvR = .ok cvRi
  hnIdx : nIdx = ms.nIdx
  /-- room for the parameters and one motive per member -/
  hroom : p.nP + p.k ≤ p.rulePrefixAt ri
  hmI : p.majorIdxAt ri = p.rulePrefixAt ri + ms.nIdx
  hopen : openPisAtFvars (p.majorIdxAt ri + 1) cvRi.type 0 = some (fvs, concl)
  hopenT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest)
  htfvs : tfvs.length = p.nP
  /-- the parameter domains, binder by binder, against the former's -/
  hparams : ∀ l, l < p.nP →
    isDefEqCore mode env F p.nP ((tfvs.map Expr.fvarTypeD).getD l default)
      (((fvs.take p.nP).map Expr.fvarTypeD).getD l default) = .ok true
  hmaj : fvs[p.majorIdxAt ri]? = some maj
  hmajFn : (Expr.fvarTypeD maj).getAppFn = Expr.const ms.cvT.name (p.lps.map .param)
  hmajLen : (Expr.fvarTypeD maj).getAppArgs.length = p.nP + ms.nIdx
  hmajParams : (Expr.fvarTypeD maj).getAppArgs.take p.nP = fvs.take p.nP
  hmajIdx : (Expr.fvarTypeD maj).getAppArgs.drop p.nP
    = (fvs.drop (p.rulePrefixAt ri)).take ms.nIdx
  hsty : inferTypeCore mode env F (p.majorIdxAt ri + 1) concl = .ok sty
  hu : ensureSortCore mode env F (p.majorIdxAt ri + 1) sty = .ok u
  /-- the elimination restriction's per-recursor half -/
  hsmall : blockLargeElimAllowed p nested = true ∨
    isDefEqCore mode env F (p.majorIdxAt ri + 1) sty (.sort .zero) = .ok true

namespace RecTyEntry

variable {F : Nat} {env : Env} {p : BlockShape} {nested : Bool} {cvTas : List ConstantVal}
  {ri : Nat} {rc : RecShape} {cvRi : ConstantVal} {nIdx : Nat} {u : Level}

/-- The rule prefix is longer than the parameters. -/
theorem nP_le (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) :
    p.nP ≤ p.rulePrefixAt ri := Nat.le_trans (Nat.le_add_right _ _) E.hroom

/-- The major-premise index is the rule prefix plus the index count. -/
theorem mI_eq (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) :
    p.majorIdxAt ri = p.rulePrefixAt ri + nIdx := E.hnIdx ▸ E.hmI

/-- The block declares a member (the recursor's), so the rule prefix
is STRICTLY longer than the parameters. -/
theorem k_pos (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) : 0 < p.k := by
  unfold BlockShape.k
  exact List.length_pos_of_mem (List.mem_of_getElem? E.hms)

theorem nP_lt (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) :
    p.nP < p.rulePrefixAt ri := by
  have := E.k_pos; have := E.hroom; omega

/-- The checked constant keeps the record's name and level parameters. -/
theorem name_eq (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) :
    cvRi.name = rc.cvR.name := (checkConstantVal_lps E.hcv).1

theorem lps_eq (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) :
    cvRi.levelParams = rc.cvR.levelParams := (checkConstantVal_lps E.hcv).2

end RecTyEntry

/-- **Stage (b), inverted**: one entry per recursor, each a
`RecTyEntry` at its own position. -/
theorem checkBlockRecTys_run {env : Env} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {F : Nat} :
    ∀ {recs : List RecShape} {ri : Nat} {cvRus : List (ConstantVal × Nat × Level)},
      checkBlockRecTys (fueledOps mode F) env p nested cvTas recs ri = .ok cvRus →
      cvRus.length = recs.length ∧
      ∀ i, i < recs.length → ∃ rc cvRi nIdx u, recs[i]? = some rc ∧
        cvRus[i]? = some (cvRi, nIdx, u) ∧
        Nonempty (RecTyEntry mode F env p nested cvTas (ri + i) rc cvRi nIdx u)
  | [], _, cvRus, h => by
    simp only [checkBlockRecTys, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | rc :: rest, ri, cvRus, h => by
    unfold checkBlockRecTys at h
    obtain ⟨ms, hms, h⟩ := exceptBind_ok h
    obtain ⟨cvTa, hcvTa, h⟩ := exceptBind_ok h
    obtain ⟨cvRi, hcv, h⟩ := exceptBind_ok h
    by_cases hroom : p.nP + p.k ≤ p.rulePrefixAt ri
    case neg => rw [if_neg hroom] at h; close_throw h
    rw [if_pos hroom] at h
    by_cases hmI : (p.majorIdxAt ri == p.rulePrefixAt ri + ms.nIdx) = true
    case neg => rw [if_neg hmI] at h; close_throw h
    rw [if_pos hmI] at h
    obtain ⟨x1, hx1, h⟩ := exceptBind_ok h
    obtain ⟨fvs, concl⟩ := x1
    obtain ⟨x2, hx2, h⟩ := exceptBind_ok h
    obtain ⟨tfvs, trest⟩ := x2
    obtain ⟨ud, hud, h⟩ := exceptBind_ok h
    obtain ⟨maj, hmaj0, h⟩ := exceptBind_ok h
    by_cases hmaj : ((Expr.fvarTypeD maj).getAppFn ==
          Expr.const ms.cvT.name (p.lps.map .param) &&
        (Expr.fvarTypeD maj).getAppArgs.length == p.nP + ms.nIdx &&
        (Expr.fvarTypeD maj).getAppArgs.take p.nP == fvs.take p.nP &&
        (Expr.fvarTypeD maj).getAppArgs.drop p.nP ==
          (fvs.drop (p.rulePrefixAt ri)).take ms.nIdx) = true
    case neg => rw [if_neg hmaj] at h; close_throw h
    rw [if_pos hmaj] at h
    obtain ⟨sty, hsty, h⟩ := exceptBind_ok h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    have hop : openPisAtFvars (p.majorIdxAt ri + 1) cvRi.type 0 = some (fvs, concl) :=
      unwrapOr_ok hx1
    have hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest) := unwrapOr_ok hx2
    have htl : tfvs.length = p.nP := Verify.openPisAtFvars_length _ hopT
    obtain ⟨-, halld⟩ := checkBlockDefEqList_inv (mode := mode)
      (what := s!"the recursor {rc.cvR.name}'s parameter domains are not the block's")
      (by cases ud; exact hud)
    simp only [Bool.and_eq_true, beq_iff_eq] at hmaj
    -- the entry, once the elimination restriction's verdict is in hand
    have key : (blockLargeElimAllowed p nested = true ∨
          isDefEqCore mode env F (p.majorIdxAt ri + 1) sty (.sort .zero) = .ok true) →
        ∀ {rs' : List (ConstantVal × Nat × Level)},
        checkBlockRecTys (fueledOps mode F) env p nested cvTas rest (ri + 1) = .ok rs' →
        cvRus = (cvRi, ms.nIdx, u) :: rs' →
        cvRus.length = (rc :: rest).length ∧
        ∀ i, i < (rc :: rest).length → ∃ rc' cvRi' nIdx' u', (rc :: rest)[i]? = some rc' ∧
          cvRus[i]? = some (cvRi', nIdx', u') ∧
          Nonempty (RecTyEntry mode F env p nested cvTas (ri + i) rc' cvRi' nIdx' u') := by
      intro hsmall rs' hrest hcv'
      subst hcv'
      obtain ⟨hlen, hall⟩ := checkBlockRecTys_run hrest
      refine ⟨by simp [hlen], fun i hi => ?_⟩
      cases i with
      | zero =>
        exact ⟨rc, cvRi, ms.nIdx, u, rfl, rfl, ⟨{
          ms := ms, cvTa := cvTa, fvs := fvs, concl := concl, tfvs := tfvs, trest := trest,
          maj := maj, sty := sty, hms := unwrapOr_ok hms, hcvTa := unwrapOr_ok hcvTa,
          hcv := hcv, hnIdx := rfl, hroom := hroom, hmI := eq_of_beq hmI, hopen := hop,
          hopenT := hopT, htfvs := htl,
          hparams := fun l hl => halld l (by rw [List.length_map, htl]; exact hl),
          hmaj := unwrapOr_ok hmaj0, hmajFn := hmaj.1.1.1, hmajLen := hmaj.1.1.2,
          hmajParams := hmaj.1.2, hmajIdx := hmaj.2, hsty := hsty, hu := hu,
          hsmall := hsmall }⟩⟩
      | succ i =>
        obtain ⟨rc', cvRi', nIdx', u', hrc, hcu, ⟨E⟩⟩ := hall i (by simpa using hi)
        refine ⟨rc', cvRi', nIdx', u', by simpa using hrc, by simpa using hcu, ⟨?_⟩⟩
        rw [show ri + (i + 1) = ri + 1 + i from by omega]
        exact E
    by_cases hlarge : blockLargeElimAllowed p nested = true
    case pos =>
      rw [if_pos hlarge] at h
      obtain ⟨rs', hrest, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact key (.inl hlarge) hrest h.symm
    case neg =>
      rw [if_neg hlarge] at h
      obtain ⟨b, hbrun, h⟩ := exceptBind_ok h
      by_cases hb : b = true
      case neg => rw [if_neg hb] at h; close_throw h
      rw [if_pos hb] at h
      obtain ⟨rs', hrest, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact key (.inr (by rw [hb] at hbrun; exact hbrun)) hrest h.symm

/-! ## Stage (b'): the family's agreements -/

/-- **`checkBlockRecIdxDomsAt`, inverted**: at every recursor the
index binder domains are the member's index telescope, opened at the
recursor's own numbering. -/
theorem checkBlockRecIdxDomsAt_inv {env : Env} {p : BlockShape}
    {cvTas : List ConstantVal} {F : Nat} :
    ∀ {l : List (ConstantVal × Nat × Level)} {ri : Nat},
      checkBlockRecIdxDomsAt (fueledOps mode F) env p cvTas l ri = .ok () →
      ∀ i, i < l.length → ∃ (cvR : ConstantVal) (nIdx : Nat) (u : Level) (cvTa : ConstantVal)
          (fvs tfvs : List Expr) (concl trest : Expr),
        l[i]? = some (cvR, nIdx, u) ∧
        cvTas[p.recTgtAt (ri + i)]? = some cvTa ∧
        openPisAtFvars (p.majorIdxAt (ri + i) + 1) cvR.type 0 = some (fvs, concl) ∧
        openPisParamsIdx p.nP nIdx (p.rulePrefixAt (ri + i)) cvTa.type
          = some (tfvs, trest) ∧
        ((tfvs.drop p.nP).map Expr.fvarTypeD).length
          = (((fvs.drop (p.rulePrefixAt (ri + i))).take nIdx).map Expr.fvarTypeD).length ∧
        ∀ q, q < ((tfvs.drop p.nP).map Expr.fvarTypeD).length →
          isDefEqCore mode env F (p.majorIdxAt (ri + i))
            (((tfvs.drop p.nP).map Expr.fvarTypeD).getD q default)
            ((((fvs.drop (p.rulePrefixAt (ri + i))).take nIdx).map Expr.fvarTypeD).getD q
              default) = .ok true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | (cvR, nIdx, u) :: rest, ri, h, i, hi => by
    unfold checkBlockRecIdxDomsAt at h
    obtain ⟨cvTa, hx0, h⟩ := exceptBind_ok h
    obtain ⟨x1, hx1, h⟩ := exceptBind_ok h
    obtain ⟨fvs, concl⟩ := x1
    obtain ⟨x2, hx2, h⟩ := exceptBind_ok h
    obtain ⟨tfvs, trest⟩ := x2
    obtain ⟨ud, hud, h⟩ := exceptBind_ok h
    cases i with
    | zero =>
      obtain ⟨hlen, hall⟩ := checkBlockDefEqList_inv (by cases ud; exact hud)
      exact ⟨cvR, nIdx, u, cvTa, fvs, tfvs, concl, trest, rfl,
        by simpa using unwrapOr_ok hx0, by simpa using unwrapOr_ok hx1,
        by simpa using unwrapOr_ok hx2, hlen, fun q hq => by simpa using hall q hq⟩
    | succ i =>
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6⟩ :=
        checkBlockRecIdxDomsAt_inv h i (by simpa using hi)
      rw [show ri + (i + 1) = ri + 1 + i from by omega]
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, by simpa using b1, b2, b3, b4, b5, b6⟩

/-- **The walk, inverted**: at every position of the tail the prefix
LENGTH is the reference's and the opened domains are defeq to it. -/
theorem checkBlockRecPrefixAt_inv {env : Env} {p : BlockShape} {rP0 F : Nat}
    {doms0 : List Expr} :
    ∀ {cvRs : List ConstantVal} {ri : Nat},
      checkBlockRecPrefixAt (fueledOps mode F) env p rP0 doms0 cvRs ri = .ok () →
      ∀ (i : Nat) (cv : ConstantVal), cvRs[i]? = some cv →
        p.rulePrefixAt (ri + i) = rP0 ∧
        ∃ (fvs : List Expr) (o : Expr),
          openPisAtFvars rP0 cv.type 0 = some (fvs, o) ∧
          doms0.length = fvs.length ∧
          ∀ l, l < doms0.length →
            isDefEqCore mode env F rP0 (doms0.getD l default)
              ((fvs.map Expr.fvarTypeD).getD l default) = .ok true
  | [], _, _, i, _, hi => by simp at hi
  | cv :: rest, ri, h, i, cvi, hi => by
    rw [checkBlockRecPrefixAt] at h
    by_cases hlen : (p.rulePrefixAt ri == rP0) = true
    case neg =>
      rw [if_neg hlen] at h
      simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
      exact nomatch h
    rw [if_pos hlen] at h
    simp only [Bind.bind, Except.bind] at h
    obtain ⟨x1, hx1, h⟩ := exceptBind_ok h
    obtain ⟨fvs, o⟩ := x1
    have hop : openPisAtFvars rP0 cv.type 0 = some (fvs, o) := unwrapOr_ok hx1
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    obtain ⟨hl, hall⟩ := checkBlockDefEqList_inv (what := "the block's recursors do not \
      share their rule prefix") (by cases u; exact hu)
    cases i with
    | zero =>
      have hcv : cv = cvi := by simpa using hi
      subst hcv
      refine ⟨by simpa using eq_of_beq hlen, fvs, o, hop, by simpa using hl, ?_⟩
      intro l hll
      exact hall l hll
    | succ i =>
      obtain ⟨hr, hrest⟩ := checkBlockRecPrefixAt_inv h i cvi (by simpa using hi)
      exact ⟨by rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hr, hrest⟩

/-- **Stage (b'), inverted**: the FIRST recursor's opening is the
reference, and every later recursor's prefix has its length and is
defeq to it binder by binder. -/
theorem checkBlockRecPrefixAgree_inv {env : Env} {p : BlockShape} {F : Nat}
    {cvRs : List ConstantVal} {cv0 : ConstantVal}
    (h : checkBlockRecPrefixAgree (fueledOps mode F) env p cvRs = .ok ())
    (h0 : cvRs[0]? = some cv0) :
    ∃ (fvs0 : List Expr) (o0 : Expr),
      openPisAtFvars (p.rulePrefixAt 0) cv0.type 0 = some (fvs0, o0) ∧
      ∀ (i : Nat) (cv : ConstantVal), cvRs[i]? = some cv → 0 < i →
        p.rulePrefixAt i = p.rulePrefixAt 0 ∧
        ∃ (fvs : List Expr) (o : Expr),
          openPisAtFvars (p.rulePrefixAt 0) cv.type 0 = some (fvs, o) ∧
          fvs0.length = fvs.length ∧
          ∀ l, l < fvs0.length →
            isDefEqCore mode env F (p.rulePrefixAt 0)
              ((fvs0.map Expr.fvarTypeD).getD l default)
              ((fvs.map Expr.fvarTypeD).getD l default) = .ok true := by
  match cvRs, h0 with
  | cv :: rest, h0 =>
    have hcv : cv = cv0 := by simpa using h0
    rw [checkBlockRecPrefixAgree] at h
    simp only [Bind.bind, Except.bind] at h
    obtain ⟨x1, hx1, h⟩ := exceptBind_ok h
    obtain ⟨fvs0, o0⟩ := x1
    have hop : openPisAtFvars (p.rulePrefixAt 0) cv0.type 0 = some (fvs0, o0) := by
      rw [← hcv]; exact unwrapOr_ok hx1
    refine ⟨fvs0, o0, hop, fun i cvi hi hipos => ?_⟩
    match i, hipos with
    | i + 1, _ =>
      obtain ⟨hr, fvs, o, hop', hlen, hall⟩ :=
        checkBlockRecPrefixAt_inv h i cvi (by simpa using hi)
      refine ⟨by rw [show i + 1 = 1 + i from by omega]; exact hr, fvs, o, hop',
        by simpa using hlen, fun l hl => ?_⟩
      have := hall l (by simpa using hl)
      simpa using this

/-- **Stage (b'), the family's agreements**, over the list stage (b)
returned: the counting half of the elimination guard, the
elimination-level PIN (D-d), the index domains and the shared rule
prefix. -/
structure RecFamRun (mode : CheckMode) (F : Nat) (env : Env) (p : BlockShape) (nested : Bool)
    (cvTas : List ConstantVal) (cvRus : List (ConstantVal × Nat × Level)) : Prop where
  /-- the block declares a family -/
  k_pos : 0 < p.k
  /-- the counting half of the elimination guard -/
  small : blockLargeElimAllowed p nested = true ∨
    ∀ u ∈ cvRus.map (·.2.2), Level.isEquiv u Level.zero = some true
  /-- the elimination-level PIN — D-d: every conclusion sort is the
  generated elimination level -/
  pin : ∀ u ∈ cvRus.map (·.2.2),
    Level.isEquiv u (structElimLevel p.elim p.large) = some true
  /-- stage (b''): the index binder domains -/
  idxDoms : checkBlockRecIdxDomsAt (fueledOps mode F) env p cvTas cvRus 0 = .ok ()
  /-- the shared rule prefix -/
  prefixAgree : checkBlockRecPrefixAgree (fueledOps mode F) env p (cvRus.map (·.1)) = .ok ()

/-- **Stage (b'), inverted.** -/
theorem checkBlockRecFamilyAgree_run {env : Env} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {cvRus : List (ConstantVal × Nat × Level)} {F : Nat}
    (h : checkBlockRecFamilyAgree (fueledOps mode F) env p nested cvTas cvRus = .ok ()) :
    RecFamRun mode F env p nested cvTas cvRus := by
  rw [checkBlockRecFamilyAgree] at h
  obtain ⟨u1, hsmall, h⟩ := exceptBind_ok h
  obtain ⟨u2, hpin, h⟩ := exceptBind_ok h
  obtain ⟨u3, hidx, h⟩ := exceptBind_ok h
  obtain ⟨hk, hs⟩ := checkBlockRecSmallElim_inv (by cases u1; exact hsmall)
  exact ⟨hk, hs,
    checkBlockRecElimPin_inv (by cases u2; exact hpin), by cases u3; exact hidx, h⟩

/-! ## Stage (c): one RULE -/

/-- **Stage (c) at ONE rule**, every bind of `checkBlockRule`'s body
named: the stream's right-hand side `rhs` is annotated into `out` (the
STORED rule), its λ-tower is compared binder by binder with the stored
recursor type's prefix and the constructor's fields, the body is
abstracted and the residue typed against the recursor's conclusion. -/
structure RuleRun (mode : CheckMode) (F : Nat) (envR envT : Env) (p : BlockShape)
    (recNames : List Name) (rlvls : List Level) (recTys : List Expr) (mIs rPs recTgts : List Nat)
    (ri : Nat) (cvR : ConstantVal) (cA : ConstantVal × Nat) (ks : List BlockFieldKind)
    (rhs out : Expr) : Type where
  recTy : Expr
  /-- the rule's own type at the rule-less recursor environment -/
  tyR : Expr
  rbs : List (Expr × BinderMeta)
  body : Expr
  fvsPref : List Expr
  oPref : Expr
  cpref : List Expr
  crest : Expr
  fvsF : List Expr
  cbody : Expr
  ldoms : List Expr
  lrest : Expr
  resid : Expr
  ihTele : Expr
  fvsIh : List Expr
  bodyO : Expr
  ty : Expr
  concl : Expr
  hrecTy : recTys[ri]? = some recTy
  hbv : rhs.looseBVarsBounded 0 = true
  hfv : rhs.hasFvar = false
  hann : annotateCore mode envR F 0 rhs = .ok out
  hlp : out.allLevelParamsDefined cvR.levelParams = true
  hres : out.constsResolve envR = true
  htyR : inferTypeCore mode envR F 0 out = .ok tyR
  hstrip : Expr.stripLams (p.rulePrefixAt ri + cA.2) out = some (rbs, body)
  hpw : ∀ b ∈ rbs, b.2.pw = Level.zeronessOf (structElimLevel p.elim p.large)
  hpref : openPisAtFvars (p.rulePrefixAt ri) recTy 0 = some (fvsPref, oPref)
  hcpar : Expr.instPisAt (fvsPref.take p.nP) cA.1.type = some (cpref, crest)
  hfld : openPisAtFvars cA.2 crest (p.rulePrefixAt ri) = some (fvsF, cbody)
  hlams : Expr.instLamsAt (fvsPref ++ fvsF) out = some (ldoms, lrest)
  /-- the λ-domains resolve at the constructors' environment -/
  hldomsRes : ∀ t ∈ ldoms, t.constsResolve envT = true
  hG2len : ((fvsPref ++ fvsF).map Expr.fvarTypeD).length = ldoms.length
  hG2 : ∀ l, l < ((fvsPref ++ fvsF).map Expr.fvarTypeD).length →
    isDefEqCore mode envT F (p.rulePrefixAt ri + cA.2)
      (((fvsPref ++ fvsF).map Expr.fvarTypeD).getD l default) (ldoms.getD l default) = .ok true
  hresid : abstractIh
      { recNames := recNames, rlvls := rlvls, mIs := mIs, rPs := rPs,
        recTgts := recTgts, nP := p.nP, rP := p.rulePrefixAt ri, nF := cA.2, ks := ks,
        teleOf := structFieldTeleOf cA.1.type p.nP cA.2,
        idxOf := structFieldIdxOf cA.1.type p.nP cA.2,
        ihKeys := blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks,
        pw := Level.zeronessOf (structElimLevel p.elim p.large) }
      0 body = some resid
  hihTele : blockIhPis p.nP (p.rulePrefixAt ri) cA.2
      (Level.zeronessOf (structElimLevel p.elim p.large))
      (fun c => recTys.getD c (.sort .zero))
      (structFieldTeleOf cA.1.type p.nP cA.2)
      (structFieldIdxOf cA.1.type p.nP cA.2)
      (blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks) 0 resid = some ihTele
  hopenIh : openPisAtFvars (blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks).length
      (ihTele.instantiateList (fvsPref ++ fvsF).reverse)
      (p.rulePrefixAt ri + cA.2) = some (fvsIh, bodyO)
  hty : inferTypeCore mode envT F
      (p.rulePrefixAt ri + cA.2 + (blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks).length)
      bodyO = .ok ty
  hconcl : Expr.instPisAtLift
      (fvsPref ++ cbody.getAppArgs.drop p.nP ++
        [Expr.mkAppN (.const cA.1.name (p.lps.map .param)) (fvsPref.take p.nP ++ fvsF)])
      recTy = some concl
  hdeq : isDefEqCore mode envT F
      (p.rulePrefixAt ri + cA.2 + (blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks).length)
      ty concl = .ok true

namespace RuleRun

variable {F : Nat} {envR envT : Env} {p : BlockShape} {recNames : List Name}
  {rlvls : List Level} {recTys : List Expr} {mIs rPs recTgts : List Nat} {ri : Nat}
  {cvR : ConstantVal} {cA : ConstantVal × Nat} {ks : List BlockFieldKind} {rhs out : Expr}

/-- The stored rule has no free variable. -/
theorem out_noFvar
    (R : RuleRun mode F envR envT p recNames rlvls recTys mIs rPs recTgts ri cvR cA ks rhs out) :
    out.hasFvar = false :=
  Expr.not_hasFvar_of_fvarsBelow_zero
    ((annotateCore_WScoped F rhs R.hann (Expr.WScoped.of_not_hasFvar R.hfv)).fvarsBelow)

/-- The stored rule is closed. -/
theorem out_bounded
    (R : RuleRun mode F envR envT p recNames rlvls recTys mIs rPs recTgts ri cvR cA ks rhs out) :
    out.looseBVarsBounded 0 = true :=
  annotateCore_looseBVars F rhs R.hann R.hbv

end RuleRun

/-- **Stage (c) at ONE rule, inverted.** -/
theorem checkBlockRule_run {envR envT : Env} {p : BlockShape} {recNames : List Name}
    {rlvls : List Level} {recTys : List Expr} {mIs rPs recTgts : List Nat} {ri : Nat}
    {cvR : ConstantVal} {cA : ConstantVal × Nat} {ks : List BlockFieldKind}
    {rhs out : Expr} {F : Nat}
    (h : checkBlockRule (fueledOps mode F) envR (fueledOps mode F) envT p recNames rlvls
      recTys mIs rPs recTgts ri cvR cA ks rhs = .ok out) :
    Nonempty (RuleRun mode F envR envT p recNames rlvls recTys mIs rPs recTgts ri cvR cA ks
      rhs out) := by
  unfold checkBlockRule at h
  obtain ⟨recTy, hrecTy, h⟩ := exceptBind_ok h
  by_cases hbv : Expr.looseBVarsBounded 0 rhs = true
  case neg => rw [if_neg hbv] at h; close_throw h
  rw [if_pos hbv] at h
  by_cases hfv : rhs.hasFvar = true
  case pos => rw [if_pos hfv] at h; close_throw h
  rw [if_neg hfv] at h
  obtain ⟨rhsA, hann, h⟩ := exceptBind_ok h
  by_cases hlp : Expr.allLevelParamsDefined cvR.levelParams rhsA = true
  case neg => rw [if_neg hlp] at h; close_throw h
  rw [if_pos hlp] at h
  by_cases hres : Expr.constsResolve envR rhsA = true
  case neg => rw [if_neg hres] at h; close_throw h
  rw [if_pos hres] at h
  obtain ⟨tyR, htyR, h⟩ := exceptBind_ok h
  obtain ⟨x1, hx1, h⟩ := exceptBind_ok h; obtain ⟨rbs, body⟩ := x1
  dsimp only at h
  by_cases hpw : rbs.all
      (fun b => b.2.pw == Level.zeronessOf (structElimLevel p.elim p.large)) = true
  case neg => rw [if_neg hpw] at h; close_throw h
  rw [if_pos hpw] at h
  obtain ⟨x2, hx2, h⟩ := exceptBind_ok h; obtain ⟨fvsPref, oPref⟩ := x2
  obtain ⟨x3, hx3, h⟩ := exceptBind_ok h; obtain ⟨cpref, crest⟩ := x3
  obtain ⟨x4, hx4, h⟩ := exceptBind_ok h; obtain ⟨fvsF, cbody⟩ := x4
  obtain ⟨x5, hx5, h⟩ := exceptBind_ok h; obtain ⟨ldoms, lrest⟩ := x5
  dsimp only at h
  by_cases hcbd : ldoms.all (fun t => Expr.constsResolve envT t) = true
  case neg => rw [if_neg hcbd] at h; close_throw h
  rw [if_pos hcbd] at h
  obtain ⟨u2, hG2, h⟩ := exceptBind_ok h
  cases u2
  obtain ⟨resid, hresid, h⟩ := exceptBind_ok h
  obtain ⟨ihTele, hihTele, h⟩ := exceptBind_ok h
  obtain ⟨x9, hx9, h⟩ := exceptBind_ok h; obtain ⟨fvsIh, bodyO⟩ := x9
  obtain ⟨ty, hty, h⟩ := exceptBind_ok h
  obtain ⟨concl, hconcl, h⟩ := exceptBind_ok h
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  by_cases hd : b = true
  case neg => rw [if_neg hd] at h; close_throw h
  subst hd
  have hout : out = rhsA := by
    simpa [pure, Except.pure] using h.symm
  subst hout
  exact ⟨{
          recTy := recTy, tyR := tyR, rbs := rbs, body := body, fvsPref := fvsPref, oPref := oPref,
          cpref := cpref, crest := crest, fvsF := fvsF, cbody := cbody, ldoms := ldoms,
          lrest := lrest, resid := resid, ihTele := ihTele, fvsIh := fvsIh, bodyO := bodyO,
          ty := ty, concl := concl,
          hrecTy := unwrapOr_ok hrecTy, hbv := hbv, hfv := Bool.not_eq_true _ |>.mp hfv,
          hann := hann, hlp := hlp, hres := hres, htyR := htyR, hstrip := unwrapOr_ok hx1,
          hpw := fun b hb => eq_of_beq ((List.all_eq_true.mp hpw) b hb),
          hpref := unwrapOr_ok hx2, hcpar := unwrapOr_ok hx3, hfld := unwrapOr_ok hx4,
          hlams := unwrapOr_ok hx5, hldomsRes := List.all_eq_true.mp hcbd,
          hG2len := (checkBlockDefEqList_inv hG2).1, hG2 := (checkBlockDefEqList_inv hG2).2,
          hresid := unwrapOr_ok hresid, hihTele := unwrapOr_ok hihTele, hopenIh := unwrapOr_ok hx9,
          hty := hty, hconcl := unwrapOr_ok hconcl, hdeq := hb }⟩

/-! ## Stage (c): one recursor's rules, and every recursor's -/

/-- **One recursor's rules**: one stored rule per (constructor, kinds)
entry and per stream right-hand side, each a `checkBlockRule` run. -/
structure RulesRun (mode : CheckMode) (F : Nat) (envR envT : Env) (p : BlockShape)
    (recNames : List Name) (rlvls : List Level) (recTys : List Expr) (mIs rPs recTgts : List Nat)
    (ri : Nat) (cvR : ConstantVal) (cs : List ((ConstantVal × Nat) × List BlockFieldKind))
    (rhss out : List Expr) : Prop where
  len : out.length = cs.length
  lenRhs : rhss.length = cs.length
  rule : ∀ (j : Nat) (q : (ConstantVal × Nat) × List BlockFieldKind) (rhs : Expr),
    cs[j]? = some q → rhss[j]? = some rhs →
    ∃ o, out[j]? = some o ∧
      checkBlockRule (fueledOps mode F) envR (fueledOps mode F) envT p recNames rlvls recTys
        mIs rPs recTgts ri cvR q.1 q.2 rhs = .ok o

/-- **One recursor's rules, inverted.** -/
theorem checkBlockRules_run {envR envT : Env} {p : BlockShape} {recNames : List Name}
    {rlvls : List Level} {recTys : List Expr} {mIs rPs recTgts : List Nat} {ri : Nat}
    {cvR : ConstantVal} {F : Nat} :
    ∀ {cs : List ((ConstantVal × Nat) × List BlockFieldKind)} {rhss out : List Expr},
      checkBlockRules (fueledOps mode F) envR (fueledOps mode F) envT p recNames
          rlvls recTys mIs rPs recTgts ri cvR cs rhss = .ok out →
      RulesRun mode F envR envT p recNames rlvls recTys mIs rPs recTgts ri cvR cs rhss out
  | [], [], out, h => by
    simp only [checkBlockRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, fun j q rhs hq _ => nomatch hq⟩
  | [], _ :: _, out, h => by
    unfold checkBlockRules at h; close_throw h
  | _ :: _, [], out, h => by
    unfold checkBlockRules at h; close_throw h
  | q0 :: cs, rhs0 :: rhss, out, h => by
    unfold checkBlockRules at h
    obtain ⟨o0, ho0, h⟩ := exceptBind_ok h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hlenR, hall⟩ := checkBlockRules_run hrest
    refine ⟨by simp [hlen], by simp [hlenR], fun j q rhs hq hrhs => ?_⟩
    cases j with
    | zero =>
      obtain rfl := Option.some.inj hq
      obtain rfl := Option.some.inj hrhs
      exact ⟨o0, rfl, ho0⟩
    | succ j =>
      obtain ⟨o, ho, hrun⟩ := hall j q rhs (by simpa using hq) (by simpa using hrhs)
      exact ⟨o, by simpa using ho, hrun⟩

/-- **Stage (c) at ONE recursor**: its member, the member's checked
constructors and field kinds, the record it was consed at, and its
rules' run. -/
structure RecRulesEntry (mode : CheckMode) (F : Nat) (envR envT : Env) (p : BlockParts)
    (recNames : List Name) (rlvls : List Level) (cvRas : List (ConstantVal × Nat))
    (ctorsAs : List (List (ConstantVal × Nat))) (ri : Nat) (rc : RecShape)
    (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) : Type where
  ms : MemberShape
  kss : List (List BlockFieldKind)
  hms : p.members[p.recTgtAt ri]? = some ms
  hctors : ctorsAs[p.recTgtAt ri]? = some r.2.2.2
  hkss : p.kinds[p.recTgtAt ri]? = some kss
  hcvRa : cvRas[ri]? = some (r.1, r.2.2.1)
  hctorsLen : r.2.2.2.length = ms.ctors.length
  hrules : checkBlockRules (fueledOps mode F) envR (fueledOps mode F) envT
      p.toBlockShape recNames rlvls (cvRas.map (·.1.type))
      ((List.range p.recs.length).map p.majorIdxAt)
      ((List.range p.recs.length).map p.rulePrefixAt) p.recTgts ri rc.cvR
      (r.2.2.2.zip kss) rc.rhss = .ok r.2.1

/-- **Every recursor's rules, inverted.** -/
theorem checkBlockRecsRules_run {envR envT : Env} {p : BlockParts} {recNames : List Name}
    {rlvls : List Level} {cvRas : List (ConstantVal × Nat)}
    {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat} :
    ∀ {recs : List RecShape} {ri : Nat}
      {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))},
      checkBlockRecsRules (fueledOps mode F) envR (fueledOps mode F) envT p
          recNames rlvls cvRas ctorsAs recs ri = .ok rs →
      rs.length = recs.length ∧
      ∀ i, i < recs.length → ∃ rc r, recs[i]? = some rc ∧ rs[i]? = some r ∧
        Nonempty (RecRulesEntry mode F envR envT p recNames rlvls cvRas ctorsAs (ri + i) rc r)
  | [], _, rs, h => by
    simp only [checkBlockRecsRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | rc :: rest, ri, rs, h => by
    unfold checkBlockRecsRules at h
    obtain ⟨ms, hms, h⟩ := exceptBind_ok h
    obtain ⟨ctorsA, hctorsA, h⟩ := exceptBind_ok h
    obtain ⟨kss, hkss, h⟩ := exceptBind_ok h
    obtain ⟨cvRn, hcvRn, h⟩ := exceptBind_ok h
    obtain ⟨cvRa, nIdx⟩ := cvRn
    try simp only at h
    by_cases hlen : (ctorsA.length == ms.ctors.length) = true
    case neg => rw [if_neg hlen] at h; close_throw h
    rw [if_pos hlen] at h
    obtain ⟨rhss, hrules, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen', hall⟩ := checkBlockRecsRules_run hrest
    refine ⟨by simp [hlen'], fun i hi => ?_⟩
    cases i with
    | zero =>
      refine ⟨rc, (cvRa, rhss, nIdx, ctorsA), rfl, rfl, ⟨{
        ms := ms, kss := kss, hms := ?_, hctors := ?_, hkss := ?_, hcvRa := ?_,
        hctorsLen := beq_iff_eq.mp hlen, hrules := ?_ }⟩⟩
      · rw [Nat.add_zero]; exact unwrapOr_ok hms
      · rw [Nat.add_zero]; exact unwrapOr_ok hctorsA
      · rw [Nat.add_zero]; exact unwrapOr_ok hkss
      · rw [Nat.add_zero]; exact unwrapOr_ok hcvRn
      · rw [Nat.add_zero]; exact hrules
    | succ i =>
      obtain ⟨rc', r, hrc, hr, ⟨E⟩⟩ := hall i (by simpa using hi)
      refine ⟨rc', r, by simpa using hrc, by simpa using hr, ⟨?_⟩⟩
      rw [show ri + (i + 1) = ri + 1 + i from by omega]
      exact E

/-! ## The whole CHECK -/

/-- **The recursor check, as run**: the stage's four binds with the
list stage (b) returned (`cvRus`), and the one bridge — the recursors
the stage STORES are the ones stage (b) CHECKED, at every index. -/
structure RecKRun (mode : CheckMode) (F : Nat) (env : Env) (p : BlockParts)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) : Type where
  /-- stage (b)'s list -/
  cvRus : List (ConstantVal × Nat × Level)
  /-- (a) the records' pins -/
  pins : checkBlockRecPins (m := CheckM) p = .ok ()
  /-- (b) every recursor's type -/
  tys : checkBlockRecTys (fueledOps mode F) env p.toBlockShape (blockNested p.kinds) cvTas
    p.recs 0 = .ok cvRus
  /-- (b') the family's agreements -/
  fam : RecFamRun mode F env p.toBlockShape (blockNested p.kinds) cvTas cvRus
  /-- (c) every recursor's rules, at the bare-`k` environment -/
  rules : checkBlockRecsRules (fueledOps mode F)
    (consBlockRecsBare p.toBlockShape 0 (cvRus.map fun q => (q.1, q.2.1)) env)
    (fueledOps mode F) env p (p.recs.map (·.cvR.name))
    ((p.recs.head?.map fun rc => rc.cvR.levelParams.map Level.param).getD [])
    (cvRus.map fun q => (q.1, q.2.1)) ctorsAs p.recs 0 = .ok rs
  lenT : cvRus.length = p.recs.length
  len : rs.length = p.recs.length
  /-- **THE BRIDGE**: the stored records are stage (b)'s -/
  stored : rs.map (fun r => (r.1, r.2.2.1)) = cvRus.map (fun q => (q.1, q.2.1))

/-- **The recursor check, inverted** — the ONE unfolding of
`checkBlockRecK`. -/
theorem checkBlockRecK_run {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRecK (fueledOps mode F) env p cvTas ctorsAs = .ok rs) :
    Nonempty (RecKRun mode F env p cvTas ctorsAs rs) := by
  unfold checkBlockRecK at h
  obtain ⟨u, hpins, h⟩ := exceptBind_ok h
  obtain ⟨cvRus, htys, h⟩ := exceptBind_ok h
  obtain ⟨uf, hfam, h⟩ := exceptBind_ok h
  obtain ⟨hlenT, -⟩ := checkBlockRecTys_run htys
  obtain ⟨hlenR, hallR⟩ := checkBlockRecsRules_run h
  refine ⟨{
          cvRus := cvRus, pins := (by cases u; exact hpins), tys := htys,
          fam := checkBlockRecFamilyAgree_run (by cases uf; exact hfam), rules := h, lenT := hlenT,
          len := hlenR, stored := ?_ }⟩
  refine List.ext_getElem? (fun i => ?_)
  by_cases hi : i < p.recs.length
  · obtain ⟨rc, r, -, hr, ⟨E⟩⟩ := hallR i hi
    have hcv := E.hcvRa
    rw [Nat.zero_add] at hcv
    simp only [List.getElem?_map] at hcv ⊢
    rw [hr]
    exact hcv.symm
  · rw [List.getElem?_eq_none (by simp only [List.length_map, hlenR]; omega),
      List.getElem?_eq_none (by simp only [List.length_map, hlenT]; omega)]

namespace RecKRun

variable {F : Nat} {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}

/-- The bare-`k` environment the rules are annotated at, spelled at
the STORED list. -/
theorem rules_stored (R : RecKRun mode F env p cvTas ctorsAs rs) :
    checkBlockRecsRules (fueledOps mode F)
      (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env)
      (fueledOps mode F) env p (p.recs.map (·.cvR.name))
      ((p.recs.head?.map fun rc => rc.cvR.levelParams.map Level.param).getD [])
      (rs.map fun r => (r.1, r.2.2.1)) ctorsAs p.recs 0 = .ok rs := by
  rw [R.stored]; exact R.rules

/-- **The bridge at an index**: stage (b)'s entry at a stored
recursor is its checked constant, with the same index count. -/
theorem stored_at (R : RecKRun mode F env p cvTas ctorsAs rs) {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[i]? = some r) :
    ∃ u, R.cvRus[i]? = some (r.1, r.2.2.1, u) := by
  have hil : i < R.cvRus.length := by
    rw [R.lenT, ← R.len]; exact (List.getElem?_eq_some_iff.mp hr).1
  refine ⟨R.cvRus[i].2.2, ?_⟩
  have h := congrArg (·[i]?) R.stored
  simp only [List.getElem?_map, hr, List.getElem?_eq_getElem hil, Option.map_some,
    Option.some.injEq, Prod.mk.injEq] at h
  rw [List.getElem?_eq_getElem hil, h.1, h.2]

/-- The bridge at an index, at the constant alone. -/
theorem stored_fst (R : RecKRun mode F env p cvTas ctorsAs rs) {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[i]? = some r) :
    (R.cvRus.map (·.1))[i]? = some r.1 := by
  obtain ⟨u, hcu⟩ := R.stored_at hr
  rw [List.getElem?_map, hcu]; rfl

/-- **Stage (b)'s entry at a STORED recursor.** -/
theorem tyAt (R : RecKRun mode F env p cvTas ctorsAs rs) {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[i]? = some r) :
    ∃ rc u, p.recs[i]? = some rc ∧ R.cvRus[i]? = some (r.1, r.2.2.1, u) ∧
      Nonempty (RecTyEntry mode F env p.toBlockShape (blockNested p.kinds) cvTas i rc r.1
        r.2.2.1 u) := by
  obtain ⟨u, hcu⟩ := R.stored_at hr
  have hil : i < p.recs.length := by rw [← R.len]; exact (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨-, hall⟩ := checkBlockRecTys_run R.tys
  obtain ⟨rc, cvRi, nIdx, u', hrc, hcu', ⟨E⟩⟩ := hall i hil
  rw [hcu] at hcu'
  obtain ⟨rfl, rfl, rfl⟩ : r.1 = cvRi ∧ r.2.2.1 = nIdx ∧ u = u' := by
    simpa using hcu'
  rw [Nat.zero_add] at E
  exact ⟨rc, u, hrc, hcu, ⟨E⟩⟩

/-- **Stage (b)'s entry at every recursor POSITION** (the stored
recursor there exists). -/
theorem tyAt' (R : RecKRun mode F env p cvTas ctorsAs rs) {i : Nat} (hi : i < p.recs.length) :
    ∃ rc r u, p.recs[i]? = some rc ∧ rs[i]? = some r ∧ R.cvRus[i]? = some (r.1, r.2.2.1, u) ∧
      Nonempty (RecTyEntry mode F env p.toBlockShape (blockNested p.kinds) cvTas i rc r.1
        r.2.2.1 u) := by
  have hi' : i < rs.length := by rw [R.len]; exact hi
  have hr : rs[i]? = some rs[i] := List.getElem?_eq_getElem hi'
  obtain ⟨rc, u, hrc, hcu, E⟩ := R.tyAt hr
  exact ⟨rc, _, u, hrc, hr, hcu, E⟩

/-- **Stage (c)'s entry at a STORED recursor.** -/
theorem rulesAt (R : RecKRun mode F env p cvTas ctorsAs rs) {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[i]? = some r) :
    ∃ rc, p.recs[i]? = some rc ∧
      Nonempty (RecRulesEntry mode F
        (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env) env p
        (p.recs.map (·.cvR.name))
        ((p.recs.head?.map fun rc => rc.cvR.levelParams.map Level.param).getD [])
        (rs.map fun r => (r.1, r.2.2.1)) ctorsAs i rc r) := by
  have hil : i < p.recs.length := by rw [← R.len]; exact (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨-, hall⟩ := checkBlockRecsRules_run R.rules_stored
  obtain ⟨rc, r', hrc, hr', ⟨E⟩⟩ := hall i hil
  obtain rfl := Option.some.inj (hr.symm.trans hr')
  rw [Nat.zero_add] at E
  exact ⟨rc, hrc, ⟨E⟩⟩

/-- The recursors' type list the rules are checked against IS the
stored recursors' types. -/
theorem recTys_eq :
    (rs.map fun r => (r.1, r.2.2.1)).map (·.1.type) = rs.map (·.1.type) := by
  simp only [List.map_map]; rfl

end RecKRun

/-- The field kinds the rule stage runs the `(c, i)`-th rule at: the
block's own, at the `c`-th recursor's member. -/
@[expose] def blockRuleKsOf (pp : BlockParts) (c i : Nat) : List BlockFieldKind :=
  (pp.kinds.getD (pp.toBlockShape.recTgtAt c) []).getD i []

namespace RecKRun

variable {F : Nat} {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}

/-- **The `(c, i)`-th rule's RUN**, with every argument PINNED to the
stored data: the rule stage's recursor-type list is the stored
recursors' types and its field kinds are `blockRuleKsOf`.  The run's
output is the stored right-hand side. -/
theorem ruleAt (R : RecKRun mode F env p cvTas ctorsAs rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) :
    ∃ rc rhs0, p.recs[c]? = some rc ∧ rc.rhss[i]? = some rhs0 ∧
      Nonempty (RuleRun mode F
        (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env) env
        p.toBlockShape (p.recs.map (·.cvR.name))
        ((p.recs.head?.map fun q => q.cvR.levelParams.map Level.param).getD [])
        (rs.map (·.1.type))
        ((List.range p.recs.length).map p.majorIdxAt)
        ((List.range p.recs.length).map p.rulePrefixAt) p.recTgts c rc.cvR cA
        (blockRuleKsOf p c i) rhs0 rhs) := by
  obtain ⟨rc, hrc, ⟨E⟩⟩ := R.rulesAt hr
  have hrun := E.hrules
  rw [RecKRun.recTys_eq] at hrun
  obtain ⟨hlenO, -, hallJ⟩ := checkBlockRules_run hrun
  have hio := (List.getElem?_eq_some_iff.mp hrhs).1
  have hz : (r.2.2.2.zip E.kss).length = min r.2.2.2.length E.kss.length := List.length_zip
  have hik : i < E.kss.length := by rw [hz] at hlenO; omega
  have hks' : (r.2.2.2.zip E.kss)[i]? = some (cA, E.kss[i]) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨hcA, List.getElem?_eq_getElem hik⟩
  obtain ⟨-, hlenI, -⟩ := checkBlockRules_run hrun
  have hil : i < rc.rhss.length := by omega
  obtain ⟨o, ho, hone⟩ := hallJ i (cA, E.kss[i]) rc.rhss[i] hks'
    (List.getElem?_eq_getElem hil)
  obtain rfl := Option.some.inj (ho.symm.trans hrhs)
  have hksEq : blockRuleKsOf p c i = E.kss[i] := by
    simp only [blockRuleKsOf, List.getD_eq_getElem?_getD, E.hkss, Option.getD_some,
      List.getElem?_eq_getElem hik]
  rw [← hksEq] at hone
  exact ⟨rc, rc.rhss[i], hrc, List.getElem?_eq_getElem hil, checkBlockRule_run hone⟩

/-- **Every constructor has its rule**, once the field kinds cover the
constructors. -/
theorem rulesLen (R : RecKRun mode F env p cvTas ctorsAs rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) : r.2.1.length = r.2.2.2.length := by
  obtain ⟨rc, -, ⟨E⟩⟩ := R.rulesAt hr
  obtain ⟨hlenO, -, -⟩ := checkBlockRules_run E.hrules
  have hk : E.kss.length = r.2.2.2.length := by
    have := hkLen _ _ E.hctors
    rwa [List.getD_eq_getElem?_getD, E.hkss, Option.getD_some] at this
  rw [hlenO, List.length_zip, hk, Nat.min_self]

/-- **A stored rule is a rule run**: every right-hand side a checked
recursor stores is the output of the `checkBlockRule` run at some
constructor of its member. -/
theorem ruleOf (R : RecKRun mode F env p cvTas ctorsAs rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {rhs : Expr} (hrhs : rhs ∈ r.2.1) :
    ∃ i cA rc rhs0, r.2.2.2[i]? = some cA ∧ r.2.1[i]? = some rhs ∧ p.recs[c]? = some rc ∧
      Nonempty (RuleRun mode F
        (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env) env
        p.toBlockShape (p.recs.map (·.cvR.name))
        ((p.recs.head?.map fun q => q.cvR.levelParams.map Level.param).getD [])
        (rs.map (·.1.type))
        ((List.range p.recs.length).map p.majorIdxAt)
        ((List.range p.recs.length).map p.rulePrefixAt) p.recTgts c rc.cvR cA
        (blockRuleKsOf p c i) rhs0 rhs) := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hrhs
  obtain ⟨rc, -, ⟨E⟩⟩ := R.rulesAt hr
  obtain ⟨hlenO, -, -⟩ := checkBlockRules_run E.hrules
  have hio := (List.getElem?_eq_some_iff.mp hi).1
  have hz : (r.2.2.2.zip E.kss).length = min r.2.2.2.length E.kss.length := List.length_zip
  have hic : i < r.2.2.2.length := by rw [hz] at hlenO; omega
  have hcA : r.2.2.2[i]? = some r.2.2.2[i] := List.getElem?_eq_getElem hic
  obtain ⟨rc', rhs0, hrc, -, hrun⟩ := R.ruleAt hr hcA hi
  exact ⟨i, _, rc', rhs0, hcA, hi, hrc, hrun⟩

end RecKRun

/-- **Stage (b)'s record at a STORED recursor, off the run.** -/
theorem checkBlockRecK_tyAt {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRecK (fueledOps mode F) env p cvTas ctorsAs = .ok rs) {i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[i]? = some r) :
    ∃ rc u, p.recs[i]? = some rc ∧
      Nonempty (RecTyEntry mode F env p.toBlockShape (blockNested p.kinds) cvTas i rc r.1
        r.2.2.1 u) := by
  obtain ⟨R⟩ := checkBlockRecK_run h
  obtain ⟨rc, u, hrc, -, E⟩ := R.tyAt hr
  exact ⟨rc, u, hrc, E⟩

/-- **One stored recursor per record.** -/
theorem checkBlockRecK_len {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRecK (fueledOps mode F) env p cvTas ctorsAs = .ok rs) :
    rs.length = p.recs.length := by
  obtain ⟨R⟩ := checkBlockRecK_run h
  exact R.len

/-- **The CHECK's own well-formedness contract**: every stored
recursor type is a CHECKED constant's, and every stored rule is the
ANNOTATED stream right-hand side, scoped at the BARE-`k` environment. -/
theorem checkBlockRecK_facts {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRecK (fueledOps mode F) env p cvTas ctorsAs = .ok rs) :
    ∀ r ∈ rs, r.1.type.hasFvar = false ∧
      r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
      r.1.type.constsResolve env = true ∧
      r.1.type.looseBVarsBounded 0 = true ∧
      ∀ rhs ∈ r.2.1, rhs.hasFvar = false ∧
        rhs.allLevelParamsDefined r.1.levelParams = true ∧
        rhs.constsResolve
          (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env) = true ∧
        rhs.looseBVarsBounded 0 = true := by
  obtain ⟨R⟩ := checkBlockRecK_run h
  intro r hr
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hr
  obtain ⟨rc, u, hrc, -, ⟨E⟩⟩ := R.tyAt hc
  obtain ⟨g1, g2, g3, g4⟩ := checkConstantVal_typeWF E.hcv
  refine ⟨g1, g2, g3, g4, fun rhs hrhs => ?_⟩
  obtain ⟨i, cA, rc', rhs0, -, -, hrc', ⟨Q⟩⟩ := R.ruleOf hc hrhs
  obtain rfl := Option.some.inj (hrc.symm.trans hrc')
  exact ⟨Q.out_noFvar, by rw [E.lps_eq]; exact Q.hlp, Q.hres, Q.out_bounded⟩

/-- **Every stored rule binds at least one variable**: recursor `j`'s
rule for a constructor with `nF` fields has the λ-prefix `rP_j + nF`,
and `rP_j > nP ≥ 0`. -/
theorem checkBlockRecK_rulePos {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRecK (fueledOps mode F) env p cvTas ctorsAs = .ok rs) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      0 < p.toBlockShape.rulePrefixAt j + cA.2 := by
  intro j r hr _ _ _
  obtain ⟨R⟩ := checkBlockRecK_run h
  obtain ⟨_, _, -, -, ⟨E⟩⟩ := R.tyAt hr
  have := E.nP_lt
  omega

/-- **The CHECK's stored recursors take no guarded name** — the stage's
own `blockRecNamesUnreserved`, transported from the RECORDS to the
constants the stage stores (`checkConstantVal` keeps a record's
name). -/
theorem checkBlockRecK_reserved {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRecK (fueledOps mode F) env p cvTas ctorsAs = .ok rs) :
    ∀ r ∈ rs, reservedRecName r.1.name = false := by
  obtain ⟨R⟩ := checkBlockRecK_run h
  intro r hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  obtain ⟨rc, u, hrc, -, ⟨E⟩⟩ := R.tyAt hi
  rw [E.name_eq]
  exact checkBlockRecPins_reserved R.pins rc (List.mem_of_getElem? hrc)

end ConLeche
