module

public import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.ExceptBind

public section

/-!
# Stage (b)'s record and the shared prefix's inversion

`RecTyEntry`: one recursor's type as checked against its MAJOR member —
the checked constant, the member's former and its parameter domains, the
major at the index binders, the conclusion's sort.  The target check's
run produces it (`recTyEntry_of_targetG`, `Verify/Inductives/RecStage.lean`),
and the stage record `RecStage` hands it out per recursor.  Also the
inversion of the family's shared rule prefix (`checkBlockRecPrefixAgree`).
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

/-- **Stage (b) at ONE recursor**.  `ri` is the recursor's position in the block, `rc` its
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
  /-- the prefix starts with the block's parameters (nothing is counted
  after them: a motive is a parameter like any other) -/
  hroom : p.nP ≤ p.rulePrefixAt ri
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
    p.nP ≤ p.rulePrefixAt ri := E.hroom

/-- The major-premise index is the rule prefix plus the index count. -/
theorem mI_eq (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) :
    p.majorIdxAt ri = p.rulePrefixAt ri + nIdx := E.hnIdx ▸ E.hmI

/-- The checked constant keeps the record's name and level parameters. -/
theorem name_eq (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) :
    cvRi.name = rc.cvR.name := (checkConstantVal_lps E.hcv).1

theorem lps_eq (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) :
    cvRi.levelParams = rc.cvR.levelParams := (checkConstantVal_lps E.hcv).2

end RecTyEntry

/-- **Stage (b) at ONE recursor, at ANY major** (lane NESTIND): the part
of `RecTyEntry` that does not name the major's inductive — the checked
constant, the prefix and the major's position, the recursor type's
openers, the conclusion's sort and the elimination half.  A nested
block's auxiliary recursor (an OUTSIDE major, a container) has it with
`nIdx` the container's index count. -/
structure RecTyGen (mode : CheckMode) (F : Nat) (env : Env) (p : BlockShape)
    (nested : Bool) (ri : Nat) (rc : RecShape) (cvRi : ConstantVal) (nIdx : Nat) (u : Level) :
    Type where
  fvs : List Expr
  concl : Expr
  maj : Expr
  sty : Expr
  hcv : checkConstantVal (fueledOps mode F) env rc.cvR = .ok cvRi
  hroom : p.nP ≤ p.rulePrefixAt ri
  hmI' : p.majorIdxAt ri = p.rulePrefixAt ri + nIdx
  hopen : openPisAtFvars (p.majorIdxAt ri + 1) cvRi.type 0 = some (fvs, concl)
  hmaj : fvs[p.majorIdxAt ri]? = some maj
  hsty : inferTypeCore mode env F (p.majorIdxAt ri + 1) concl = .ok sty
  hu : ensureSortCore mode env F (p.majorIdxAt ri + 1) sty = .ok u
  hsmall : blockLargeElimAllowed p nested = true ∨
    isDefEqCore mode env F (p.majorIdxAt ri + 1) sty (.sort .zero) = .ok true

/-- A member entry's major-free part. -/
def RecTyEntry.toGen {F : Nat} {env : Env} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ri : Nat} {rc : RecShape} {cvRi : ConstantVal} {nIdx : Nat}
    {u : Level} (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) :
    RecTyGen mode F env p nested ri rc cvRi nIdx u :=
  { fvs := E.fvs, concl := E.concl, maj := E.maj, sty := E.sty, hcv := E.hcv,
    hroom := E.hroom, hmI' := E.mI_eq, hopen := E.hopen, hmaj := E.hmaj, hsty := E.hsty,
    hu := E.hu, hsmall := E.hsmall }

namespace RecTyGen

variable {F : Nat} {env : Env} {p : BlockShape} {nested : Bool}
  {ri : Nat} {rc : RecShape} {cvRi : ConstantVal} {nIdx : Nat} {u : Level}

theorem nP_le (E : RecTyGen mode F env p nested ri rc cvRi nIdx u) :
    p.nP ≤ p.rulePrefixAt ri := E.hroom

theorem mI_eq (E : RecTyGen mode F env p nested ri rc cvRi nIdx u) :
    p.majorIdxAt ri = p.rulePrefixAt ri + nIdx := E.hmI'

theorem name_eq (E : RecTyGen mode F env p nested ri rc cvRi nIdx u) :
    cvRi.name = rc.cvR.name := (checkConstantVal_lps E.hcv).1

theorem lps_eq (E : RecTyGen mode F env p nested ri rc cvRi nIdx u) :
    cvRi.levelParams = rc.cvR.levelParams := (checkConstantVal_lps E.hcv).2

end RecTyGen

/-! ## Stage (b'): the family's agreements -/

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

end ConLeche
