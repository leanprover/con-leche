module

public import ConLeche.Verify.Inductives.FixWF
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.Shift

public section

/-!
# The uniform install: environment well-formedness at k members
(the uniform inductive route, milestone M4)

`EnvWF` for the environments `checkBlock` walks through — `FixWF.lean`
and `SumWF.lean` at k members:

* **the k formers consed at once** (`envWF_consBlockInds`,
  `direct_block_inds_wf`), each with ITS capability record at the
  block's `is_rec` verdict; the record names the parameter count as its
  arity (`blockCapsAt_arity`, `blockCaps_arity`), which is what makes
  `IndCapsWF` hold at every former's cons;
* **the N constructors consed, member by member**
  (`envWF_consBlockCtors`, `direct_block_ctors_wf`);
* **the k recursors consed at once, with their rules**
  (`envWF_consBlockRecs`), each rule's right-hand side scoped by the
  recursor stage at the BARE-`k` environment — the one holding all `k`
  RULE-LESS recursors, which finds exactly the names the stored cons
  finds (`find?_consBlockRecs_of_bare`); the rules themselves are
  `sumRules`' per recursor, so `sumRules_mem`/`sumRules_bits`
  (`SumWF.lean`) are the block's rule facts unchanged;
* **the projection tables** (`direct_block_tables_wf`).

`checkBlockRec_facts` is the recursor stage's WF contract, proved at
EITHER setting of the stage's gate (`blockRecCheckOn`, split on rather
than unfolded): with the gate down at ONE member the existing
generate-and-compare's (`checkNativeRec_facts`) and at two or more
vacuous, with the gate lifted the CHECK's own
(`checkBlockRecK_facts`, off `checkBlockRecTys_inv` /
`checkBlockRule_facts` / `checkBlockRules_facts` /
`checkBlockRecsRules_facts`).

**Why the recursors are consed SIMULTANEOUSLY** (milestone M6's entry
cost): the CHECK's rules are MUTUALLY recursive — a rule of `rec_0`
may name `rec_1` — so a right-hand side resolves at the environment
holding ALL `k` rule-less recursors and at no environment holding
`rec_0` alone.  `EnvWF`'s recursor clause is checked at the
environment each constant is consed into, so the one-at-a-time
`EnvWF.cons` induction cannot close at `k ≥ 2`; `EnvWF E` is
`∀ c ∈ E.consts, ConstWF E c`, which is provable at the FINAL
environment directly (`mem_consBlockRecs`, `ConstWF.mono`).
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

/-! ## The capability record's arity -/

/-- **The block's capability record names the parameter count as its
arity** (`nativeCapsAt_arity` at a member): what establishes
`IndCapsWF` at every former's cons. -/
theorem blockCapsAt_arity (p : BlockShape) (mi : Nat) (isRec : Bool) :
    ((blockCapsAt p mi isRec).unitlike = true → (blockCapsAt p mi isRec).unitParams = p.nP) ∧
    ((blockCapsAt p mi isRec).eta = true → (blockCapsAt p mi isRec).etaParams = p.nP) := by
  unfold blockCapsAt
  split
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- `blockCapsAt_arity` at the classified verdict. -/
theorem blockCaps_arity (p : BlockParts) (mi : Nat) :
    ((blockCaps p mi).unitlike = true → (blockCaps p mi).unitParams = p.nP) ∧
    ((blockCaps p mi).eta = true → (blockCaps p mi).etaParams = p.nP) :=
  blockCapsAt_arity p.toBlockShape mi (blockIsRec p.kinds)

/-! ## Stage 1: the k formers consed at once -/

/-- Resolution carries along the members' formers' conses. -/
theorem constsResolve_consBlockInds {p₁ : BlockShape} {isRec : Bool} {e : Expr} :
    ∀ {cvTas : List ConstantVal} {i : Nat} {env : Env},
      e.constsResolve env = true →
      e.constsResolve (consBlockInds p₁ isRec cvTas i env) = true
  | [], _, _, h => h
  | _ :: _, _, _, h => by
    simp only [consBlockInds]
    exact constsResolve_consBlockInds (Expr.constsResolve_mono h)

/-- **One former's cons keeps well-formedness**: the stored former is a
checked constant whose telescope strips at the parameter count, which is
the capability record's arity. -/
theorem envWF_cons_blockInd {p₁ : BlockShape} {isRec : Bool} {i : Nat} {env : Env}
    {cvTa : ConstantVal} (henv : EnvWF env)
    (h1 : cvTa.type.hasFvar = false)
    (h2 : cvTa.type.allLevelParamsDefined cvTa.levelParams = true)
    (h3 : cvTa.type.constsResolve env = true)
    (h4 : cvTa.type.looseBVarsBounded 0 = true)
    (h5 : (cvTa.type.stripPis p₁.nP).isSome = true) :
    EnvWF ⟨.indInfo cvTa (blockCapsAt p₁ i isRec) :: env.consts⟩ := by
  refine EnvWF.cons henv (structConstWF h1 h2 (Expr.constsResolve_mono h3) h4
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (by intro tbl hh; exact ConstantInfo.noConfusion hh) ?_)
  refine IndCapsWF.of_caps ?_ ?_
  · intro hu; rw [(blockCapsAt_arity p₁ i isRec).1 hu]; exact h5
  · intro he; rw [(blockCapsAt_arity p₁ i isRec).2 he]; exact h5

/-- **The k formers' conses keep well-formedness.** -/
theorem envWF_consBlockInds {p₁ : BlockShape} {isRec : Bool} :
    ∀ {cvTas : List ConstantVal} {i : Nat} {env : Env},
      EnvWF env →
      (∀ cvTa ∈ cvTas, cvTa.type.hasFvar = false ∧
        cvTa.type.allLevelParamsDefined cvTa.levelParams = true ∧
        cvTa.type.constsResolve env = true ∧
        cvTa.type.looseBVarsBounded 0 = true ∧
        (cvTa.type.stripPis p₁.nP).isSome = true) →
      EnvWF (consBlockInds p₁ isRec cvTas i env)
  | [], _, _, henv, _ => henv
  | cvTa :: rest, i, env, henv, hall => by
    simp only [consBlockInds]
    refine envWF_consBlockInds ?_ ?_
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hall cvTa List.mem_cons_self
      exact envWF_cons_blockInd henv h1 h2 h3 h4 h5
    · intro cvTa' hc'
      obtain ⟨h1, h2, h3, h4, h5⟩ := hall cvTa' (List.mem_cons_of_mem _ hc')
      exact ⟨h1, h2, Expr.constsResolve_mono h3, h4, h5⟩

/-- **Stage 1 at the run level**: the environment holding the k formers
is well-formed, and every annotated former's type is closed. -/
theorem direct_block_inds_wf {env envI : Env} (henv : EnvWF env)
    {p : BlockParts} {isRec : Bool} {cvTas : List ConstantVal} {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, cvTas, p₁)) :
    EnvWF envI ∧ ∀ cvTa ∈ cvTas, cvTa.type.hasFvar = false := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, rfl, rfl, rfl, hq, hcvs, -⟩ :=
    checkBlockInds_shape h
  have key : ∀ cvTa ∈ cvTa0 :: cvs.map (·.1),
      cvTa.type.hasFvar = false ∧
      cvTa.type.allLevelParamsDefined cvTa.levelParams = true ∧
      cvTa.type.constsResolve env = true ∧
      cvTa.type.looseBVarsBounded 0 = true ∧
      (cvTa.type.stripPis (p.toBlockShape.withSort s0).nP).isSome = true := by
    intro cvTa hcv
    have step : ∀ (ms : MemberShape) (s : Level),
        checkBlockTele (fueledOps mode F) env p.nP ms = .ok (cvTa, s) →
        cvTa.type.hasFvar = false ∧
        cvTa.type.allLevelParamsDefined cvTa.levelParams = true ∧
        cvTa.type.constsResolve env = true ∧
        cvTa.type.looseBVarsBounded 0 = true ∧
        (cvTa.type.stripPis (p.toBlockShape.withSort s0).nP).isSome = true := by
      intro ms s hte
      obtain ⟨cvT, -, -, hccv, bs, hstrip⟩ := checkBlockTele_shape hte
      obtain ⟨g1, g2, g3, g4⟩ := checkConstantVal_typeWF hccv
      refine ⟨g1, g2, g3, g4, ?_⟩
      refine stripPis_isSome_of_le (n := p.nP + ms.nIdx) (Nat.le_add_right _ _) ?_
      rw [hstrip]; rfl
    simp only [List.mem_cons] at hcv
    rcases hcv with rfl | hcv
    · exact step ms0 s0 hq
    · obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hcv
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hq'
      obtain ⟨hlen, hall⟩ := checkBlockTeles_inv hcvs
      have hil : i < rest.length := by
        rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨q', hq'', hte⟩ := hall i rest[i] (List.getElem?_eq_getElem hil)
      obtain rfl := Option.some.inj (hi.symm.trans hq'')
      exact step rest[i] q.2 hte
  exact ⟨envWF_consBlockInds henv key, fun cvTa hcv => (key cvTa hcv).1⟩

/-! ## Stage 1b: the constructors consed, member by member -/

/-- Resolution carries along one member's constructors' conses. -/
theorem constsResolve_consSumCtors {nP : Nat} {e : Expr} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      e.constsResolve env = true → e.constsResolve (consSumCtors nP ctorsA env) = true
  | [], _, h => h
  | _ :: _, _, h => by
    simp only [consSumCtors]
    exact constsResolve_consSumCtors (Expr.constsResolve_mono h)

/-- Resolution carries along all the members' constructors' conses. -/
theorem constsResolve_consBlockCtors {nP : Nat} {e : Expr} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env : Env},
      e.constsResolve env = true → e.constsResolve (consBlockCtors nP ctorsAs env) = true
  | [], _, h => h
  | _ :: _, _, h => by
    simp only [consBlockCtors]
    exact constsResolve_consBlockCtors (constsResolve_consSumCtors h)

/-- **The members' constructors' conses keep well-formedness**
(`envWF_consSumCtors` at k members). -/
theorem envWF_consBlockCtors {nP : Nat} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env : Env},
      EnvWF env →
      (∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, c.1.type.hasFvar = false ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true) →
      EnvWF (consBlockCtors nP ctorsAs env)
  | [], _, henv, _ => henv
  | ctorsA :: rest, env, henv, hall => by
    simp only [consBlockCtors]
    refine envWF_consBlockCtors
      (envWF_consSumCtors henv (hall ctorsA List.mem_cons_self)) ?_
    intro ctorsA' hc' c hc
    obtain ⟨h1, h2, h3, h4⟩ := hall ctorsA' (List.mem_cons_of_mem _ hc') c hc
    exact ⟨h1, h2, constsResolve_consSumCtors h3, h4⟩

/-- **Stage 1b at the run level**: the environment holding the k
formers and all the constructors is well-formed. -/
theorem direct_block_ctors_wf {env₀ env₁ : Env} (henv : EnvWF env₁)
    {q : BlockShape} {l : List (MemberShape × ConstantVal)}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    {nP F : Nat}
    (h : checkBlockCtors (fueledOps mode F) env₀ env₁ q l = .ok (ctorsAs, sortsss)) :
    EnvWF (consBlockCtors nP ctorsAs env₁) := by
  obtain ⟨hlen, -, hall⟩ := checkBlockCtors_inv h
  refine envWF_consBlockCtors henv ?_
  intro ctorsA hcA c hc
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hcA
  have hil : i < l.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨ctorsA', sortss, hcA', -, hcs⟩ := hall i l[i] (List.getElem?_eq_getElem hil)
  obtain rfl := Option.some.inj (hi.symm.trans hcA')
  obtain ⟨-, -, hallc⟩ := checkSumCtors_inv hcs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  have hjl : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjl' : j < l[i].1.ctors.length := by
    obtain ⟨hlc, -, -⟩ := checkSumCtors_inv hcs
    omega
  obtain ⟨-, sorts, -, hctor⟩ :=
    hallc j l[i].1.ctors[j] c (List.getElem?_eq_getElem hjl') hj
  exact direct_sum_ctor_typeWF hctor

/-! ## The CHECK, inverted (lane V2 scratch) -/

private theorem vThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

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

theorem checkBlockRule_facts {envR envT : Env} {p : BlockShape} {recNames : List Name}
    {rlvls : List Level} {recTys : List Expr} {mIs rPs recTgts : List Nat} {ri : Nat}
    {cvR : ConstantVal} {cA : ConstantVal × Nat} {ks : List BlockFieldKind}
    {rhs out : Expr} {F : Nat}
    (h : checkBlockRule (fueledOps mode F) envR (fueledOps mode F) envT p recNames rlvls
      recTys mIs rPs recTgts ri cvR cA ks rhs = .ok out) :
    out.hasFvar = false ∧
    out.allLevelParamsDefined cvR.levelParams = true ∧
    out.constsResolve envR = true ∧
    out.looseBVarsBounded 0 = true := by
  unfold checkBlockRule at h
  obtain ⟨recTy, _, h⟩ := exceptBind_ok h
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
  -- the rule's own typing at the rule-less recursor environment
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨x1, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x1
  obtain ⟨x2, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x2
  obtain ⟨x3, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x3
  obtain ⟨x4, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x4
  obtain ⟨x5, _, h⟩ := exceptBind_ok h; obtain ⟨ldoms, lrest⟩ := x5
  dsimp only at h
  -- the rule's λ-domains resolve at the CONSTRUCTORS' environment
  by_cases hcbd : ldoms.all (fun t => Expr.constsResolve envT t) = true
  case neg => rw [if_neg hcbd] at h; close_throw h
  rw [if_pos hcbd] at h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨x9, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x9
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨b, _, h⟩ := exceptBind_ok h
  by_cases hd : b = true
  case neg => rw [if_neg hd] at h; close_throw h
  rw [if_pos hd] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hann' : annotateCore mode envR F 0 rhs = .ok rhsA := hann
  refine ⟨?_, hlp, hres, annotateCore_looseBVars F rhs hann' hbv⟩
  exact Expr.not_hasFvar_of_fvarsBelow_zero
    ((annotateCore_WScoped F rhs hann'
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ |>.mp hfv))).fvarsBelow)


/-- A checked constant keeps the record's name and level parameters:
only its type is replaced, by the annotated one. -/
theorem checkConstantVal_lps {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : checkConstantVal (fueledOps mode F) env cv = .ok cvA) :
    cvA.name = cv.name ∧ cvA.levelParams = cv.levelParams := by
  unfold checkConstantVal at h
  by_cases h1 : (env.find? cv.name).isSome = true
  · rw [if_pos h1] at h; close_throw h
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [if_pos h2] at h; close_throw h
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [if_pos h3] at h; close_throw h
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; close_throw h
  rw [if_pos h4] at h
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [if_neg h5] at h; close_throw h
  rw [if_pos h5] at h
  by_cases h6 : cv.type.hasFvar = true
  · rw [if_pos h6] at h; close_throw h
  rw [if_neg h6] at h
  obtain ⟨type, _, h⟩ := exceptBind_ok h
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams type = true
  case neg => rw [if_neg h7] at h; close_throw h
  rw [if_pos h7] at h
  by_cases h8 : Expr.constsResolve env type = true
  case neg => rw [if_neg h8] at h; close_throw h
  rw [if_pos h8] at h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

/-- **Stage (b), inverted**: one entry per RECURSOR, its constant
checked at the block's environment. -/
theorem checkBlockRecTys_inv {env : Env} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {F : Nat} :
    ∀ {recs : List RecShape} {ri : Nat} {cvRus : List (ConstantVal × Nat × Level)},
      checkBlockRecTys (fueledOps mode F) env p nested cvTas recs ri = .ok cvRus →
      cvRus.length = recs.length ∧
      ∀ i, i < recs.length → ∃ rc cvRi nIdx u, recs[i]? = some rc ∧
        cvRus[i]? = some (cvRi, nIdx, u) ∧
        checkConstantVal (fueledOps mode F) env rc.cvR = .ok cvRi ∧
        p.nP ≤ p.rulePrefixAt (ri + i) ∧
        p.majorIdxAt (ri + i) = p.rulePrefixAt (ri + i) + nIdx
  | [], _, cvRus, h => by
    simp only [checkBlockRecTys, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | rc :: rest, ri, cvRus, h => by
    unfold checkBlockRecTys at h
    obtain ⟨ms, _, h⟩ := exceptBind_ok h
    obtain ⟨cvTa, _, h⟩ := exceptBind_ok h
    obtain ⟨cvRi, hcv, h⟩ := exceptBind_ok h
    by_cases hle : p.nP ≤ p.rulePrefixAt ri
    case neg => rw [if_neg hle] at h; close_throw h
    rw [if_pos hle] at h
    by_cases hle2 : (p.majorIdxAt ri == p.rulePrefixAt ri + ms.nIdx) = true
    case neg => rw [if_neg hle2] at h; close_throw h
    rw [if_pos hle2] at h
    obtain ⟨x1, _, h⟩ := exceptBind_ok h; obtain ⟨fvs, concl⟩ := x1
    obtain ⟨x2, _, h⟩ := exceptBind_ok h; obtain ⟨_, _⟩ := x2
    obtain ⟨_, _, h⟩ := exceptBind_ok h
    obtain ⟨maj, _, h⟩ := exceptBind_ok h
    by_cases hmaj : (maj.fvarTypeD.getAppFn == Expr.const ms.cvT.name (p.lps.map .param) &&
        maj.fvarTypeD.getAppArgs.length == p.nP + ms.nIdx &&
        maj.fvarTypeD.getAppArgs.take p.nP == fvs.take p.nP &&
        maj.fvarTypeD.getAppArgs.drop p.nP ==
          (fvs.drop (p.rulePrefixAt ri)).take ms.nIdx) = true
    case neg => rw [if_neg hmaj] at h; close_throw h
    rw [if_pos hmaj] at h
    obtain ⟨sty, _, h⟩ := exceptBind_ok h
    obtain ⟨u, _, h⟩ := exceptBind_ok h
    by_cases hlarge : blockLargeElimAllowed p nested = true
    case pos =>
      rw [if_pos hlarge] at h
      obtain ⟨rs', hrest, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hlen, hall⟩ := checkBlockRecTys_inv hrest
      refine ⟨by simp [hlen], ?_⟩
      intro i hi
      cases i with
      | zero => exact ⟨rc, cvRi, ms.nIdx, u, rfl, rfl, hcv, hle, by
          simpa using eq_of_beq hle2⟩
      | succ i =>
        obtain ⟨rc', cvRi', nIdx', u', hrc, hcu, hcv', hle', hle2'⟩ := hall i (by simpa using hi)
        refine ⟨rc', cvRi', nIdx', u', by simpa using hrc, by simpa using hcu, hcv', ?_, ?_⟩
        · rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hle'
        · rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hle2'
    case neg =>
      rw [if_neg hlarge] at h
      obtain ⟨b, _, h⟩ := exceptBind_ok h
      by_cases hb : b = true
      case neg => rw [if_neg hb] at h; close_throw h
      rw [if_pos hb] at h
      obtain ⟨rs', hrest, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hlen, hall⟩ := checkBlockRecTys_inv hrest
      refine ⟨by simp [hlen], ?_⟩
      intro i hi
      cases i with
      | zero => exact ⟨rc, cvRi, ms.nIdx, u, rfl, rfl, hcv, hle, by
          simpa using eq_of_beq hle2⟩
      | succ i =>
        obtain ⟨rc', cvRi', nIdx', u', hrc, hcu, hcv', hle', hle2'⟩ := hall i (by simpa using hi)
        refine ⟨rc', cvRi', nIdx', u', by simpa using hrc, by simpa using hcu, hcv', ?_, ?_⟩
        · rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hle'
        · rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hle2'

/-- One recursor's rules: every stored right-hand side is the
ANNOTATED stream one, scoped at the bare-`k` environment. -/
theorem checkBlockRules_facts {envR envT : Env} {p : BlockShape} {recNames : List Name}
    {rlvls : List Level} {recTys : List Expr} {mIs rPs recTgts : List Nat} {ri : Nat}
    {cvR : ConstantVal} {F : Nat} :
    ∀ {cs : List ((ConstantVal × Nat) × List BlockFieldKind)} {rhss out : List Expr},
      checkBlockRules (fueledOps mode F) envR (fueledOps mode F) envT p recNames rlvls
        recTys mIs rPs recTgts ri cvR cs rhss = .ok out →
      ∀ rhs ∈ out, rhs.hasFvar = false ∧
        rhs.allLevelParamsDefined cvR.levelParams = true ∧
        rhs.constsResolve envR = true ∧ rhs.looseBVarsBounded 0 = true
  | [], [], out, h => by
    simp only [checkBlockRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro rhs hrhs
    simp at hrhs
  | (cA, ks) :: cs, rhs0 :: rhss, out, h => by
    unfold checkBlockRules at h
    obtain ⟨r, hr, h⟩ := exceptBind_ok h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro rhs hrhs
    rcases List.mem_cons.mp hrhs with rfl | hmem
    · exact checkBlockRule_facts hr
    · exact checkBlockRules_facts hrest rhs hmem
  | [], _ :: _, out, h => by
    simp only [checkBlockRules] at h
    close_throw h
  | _ :: _, [], out, h => by
    simp only [checkBlockRules] at h
    close_throw h

/-- **Stage (c), inverted**: one entry per RECURSOR, at the recursor's
own checked constant, with every rule's right-hand side scoped at the
bare-`k` environment. -/
theorem checkBlockRecsRules_facts {envR envT : Env} {p : BlockParts} {recNames : List Name}
    {rlvls : List Level} {cvRas : List (ConstantVal × Nat)}
    {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat} :
    ∀ {recs : List RecShape} {ri : Nat}
      {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))},
      checkBlockRecsRules (fueledOps mode F) envR (fueledOps mode F) envT p recNames rlvls
        cvRas ctorsAs recs ri = .ok rs →
      rs.length = recs.length ∧
      ∀ i, i < recs.length → ∃ rc r, recs[i]? = some rc ∧ rs[i]? = some r ∧
        cvRas[ri + i]? = some (r.1, r.2.2.1) ∧
        ∀ rhs ∈ r.2.1, rhs.hasFvar = false ∧
          rhs.allLevelParamsDefined rc.cvR.levelParams = true ∧
          rhs.constsResolve envR = true ∧ rhs.looseBVarsBounded 0 = true
  | [], _, rs, h => by
    simp only [checkBlockRecsRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | rc :: rest, ri, rs, h => by
    unfold checkBlockRecsRules at h
    obtain ⟨ms, _, h⟩ := exceptBind_ok h
    obtain ⟨ctorsA, _, h⟩ := exceptBind_ok h
    obtain ⟨kss, _, h⟩ := exceptBind_ok h
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
    obtain ⟨hlen', hall⟩ := checkBlockRecsRules_facts hrest
    refine ⟨by simp [hlen'], ?_⟩
    intro i hi
    cases i with
    | zero =>
      refine ⟨rc, (cvRa, rhss, nIdx, ctorsA), rfl, rfl, by simpa using unwrapOr_ok hcvRn, ?_⟩
      exact checkBlockRules_facts hrules
    | succ i =>
      obtain ⟨rc', r', hrc, hr, hcv, hfacts⟩ := hall i (by simpa using hi)
      refine ⟨rc', r', by simpa using hrc, by simpa using hr, ?_, hfacts⟩
      have he : ri + 1 + i = ri + (i + 1) := by omega
      rw [he] at hcv
      exact hcv

/-! ## The recursor stage's well-formedness contract -/

/-- **The CHECK's own well-formedness contract** (milestone M5's stage
at any number of members): every stored recursor type is a CHECKED
constant's, and every stored rule is the ANNOTATED stream right-hand
side, scoped at the BARE-`k` environment — the one holding all `k`
rule-less recursors, which is where stage (c) annotates and resolves
it. -/
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
  unfold checkBlockRecK at h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨cvRus, htys, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨hlenT, hallT⟩ := checkBlockRecTys_inv htys
  obtain ⟨hlenR, hallR⟩ := checkBlockRecsRules_facts h
  -- the `k` recursor records the stage consed ARE the stored ones
  have hmap : rs.map (fun r => (r.1, r.2.2.1)) = cvRus.map (fun q => (q.1, q.2.1)) := by
    refine List.ext_getElem? (fun i => ?_)
    by_cases hi : i < p.recs.length
    · obtain ⟨rc, r, -, hr, hcv, -⟩ := hallR i hi
      rw [Nat.zero_add] at hcv
      simp only [List.getElem?_map] at hcv ⊢
      rw [hr]
      exact hcv.symm
    · have h1 : (rs.map (fun r => (r.1, r.2.2.1))).length ≤ i := by
        simp only [List.length_map, hlenR]; omega
      have h2 : (cvRus.map (fun q => (q.1, q.2.1))).length ≤ i := by
        simp only [List.length_map, hlenT]; omega
      rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]
  intro r hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  have hil : i < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨rc, r', hrc, hr', hcvRa, hfacts⟩ := hallR i hil
  obtain rfl := Option.some.inj (hi.symm.trans hr')
  obtain ⟨rc'', cvRi, nIdx, u, hrc'', hcu, hcv, -, -⟩ := hallT i hil
  obtain rfl := Option.some.inj (hrc.symm.trans hrc'')
  have hcvRa' : (cvRus.map (fun q => (q.1, q.2.1)))[i]? = some (cvRi, nIdx) := by
    rw [List.getElem?_map, hcu]; rfl
  have hr1 : r.1 = cvRi := by
    have := hcvRa
    rw [Nat.zero_add] at this
    exact congrArg Prod.fst (Option.some.inj (this.symm.trans hcvRa'))
  obtain ⟨g1, g2, g3, g4⟩ := checkConstantVal_typeWF hcv
  obtain ⟨-, glp⟩ := checkConstantVal_lps hcv
  rw [hr1]
  refine ⟨g1, g2, g3, g4, ?_⟩
  intro rhs hrhs
  obtain ⟨f1, f2, f3, f4⟩ := hfacts rhs hrhs
  refine ⟨f1, by rw [glp]; exact f2, ?_, f4⟩
  rw [hmap]
  exact f3

/-- **The recursor stage's stored pieces**, as its own guards checked
them — at EITHER setting of the stage's gate (`blockRecCheckOn`): with
the gate down at ONE member the existing generate-and-compare's
(`checkNativeRec_facts`), at two or more the stage declines; with it
lifted the CHECK's own (`checkBlockRecK_facts`).

The rules' scoping clause is stated at the BARE-`k` environment
`consBlockRecsBare … env` — the environment holding all `k`
RULE-LESS recursors, which is where the new stage annotates, resolves
and scopes a rule's right-hand side.  It has to be: the CHECK's rules
are MUTUALLY recursive, so a rule of `rec_0` may name `rec_1` and
resolves at no environment holding `rec_0` alone.  `EnvWF`'s recursor
clause is checked at the environment the constant is consed into, so
`envWF_consBlockRecs` below is a SIMULTANEOUS cons. -/
theorem checkBlockRec_facts {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRec (fueledOps mode F) env p cvTas ctorsAs = .ok rs) :
    ∀ r ∈ rs, r.1.type.hasFvar = false ∧
      r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
      r.1.type.constsResolve env = true ∧
      r.1.type.looseBVarsBounded 0 = true ∧
      ∀ rhs ∈ r.2.1, rhs.hasFvar = false ∧
        rhs.allLevelParamsDefined r.1.levelParams = true ∧
        rhs.constsResolve
          (consBlockRecsBare p.toBlockShape 0 (rs.map fun r => (r.1, r.2.2.1)) env) = true ∧
        rhs.looseBVarsBounded 0 = true := by
  by_cases hg : blockRecCheckOn = true
  · unfold checkBlockRec at h
    rw [if_pos hg] at h
    exact checkBlockRecK_facts h
  unfold checkBlockRec at h
  rw [if_neg hg] at h
  split at h
  case h_2 =>
    exfalso
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals exact nomatch h
  case h_1 ms cvTa ctorsA hms hcvTas hctorsAs =>
  simp only [bind, Except.bind] at h
  split at h
  case isFalse => exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  case isTrue =>
  obtain ⟨r0, hrec, h⟩ := exceptBind_ok h
  obtain ⟨cvRa, rhss⟩ := r0
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨-, -, ⟨htf, htp, htr, htb⟩, -, hall⟩ := checkNativeRec_facts hrec
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  refine ⟨htf, htp, htr, htb, ?_⟩
  intro rhs hrhs
  obtain ⟨g1, g2, g3, g4⟩ := hall rhs hrhs
  refine ⟨g1, g2, ?_, g4⟩
  simp only [List.map_cons, List.map_nil, consBlockRecsBare]
  exact Expr.constsResolve_of_find
    (find?_isSome_cons_same (c := .recInfo cvRa p.toNative.majorIdx p.toNative.rulePrefix [])
      (c' := .recInfo cvRa (p.toBlockShape.majorIdxAt 0) (p.toBlockShape.rulePrefixAt 0) [])
      rfl) g3

/-! ## The k recursors consed with their rules, SIMULTANEOUSLY -/

/-- Well-formedness of a stored constant transfers along a lookup
dominance: every clause of `ConstWF` depends on the environment only
through `constsResolve`, and the capability arities not at all. -/
theorem ConstWF.mono {envA envB : Env}
    (hf : ∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true)
    {c : ConstantInfo} (h : ConstWF envA c) : ConstWF envB c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩ := h
  refine ⟨h1, h2, Expr.constsResolve_le hf h3, h4, fun cv value hint heq =>
    let ⟨g1, g2, g3, g4⟩ := h5 cv value hint heq
    ⟨g1, g2, Expr.constsResolve_le hf g3, g4⟩, ?_,
    fun tbl heq =>
      let ⟨g0, g⟩ := h8 tbl heq
      ⟨g0, fun i b hb =>
        let ⟨g1, g2, g3, g4⟩ := g i b hb
        ⟨g1, g2, Expr.constsResolve_le hf g3, g4⟩⟩, h9⟩
  intro cv mI rP rules heq r hr
  obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv mI rP rules heq r hr
  refine ⟨g1, g2, Expr.constsResolve_le hf g3, g4, ?_⟩
  intro lvls pins hfr
  obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hfr
  exact ⟨n1, n2, fun pin hpin =>
    let ⟨p1, p2, p3, p4⟩ := n3 pin hpin
    ⟨p1, p2, Expr.constsResolve_le hf p3, p4⟩, n4⟩

/-- A name found above one cons is found above two. -/
theorem find?_isSome_cons_under {a b : ConstantInfo} {env : Env} (n : Name)
    (h : (Env.find? ⟨a :: env.consts⟩ n).isSome = true) :
    (Env.find? ⟨a :: b :: env.consts⟩ n).isSome = true := by
  rw [Env.find?_cons] at h
  show (Env.find? ⟨a :: (Env.mk (b :: env.consts)).consts⟩ n).isSome = true
  rw [Env.find?_cons]
  split at h
  · next hn => rw [if_pos hn]; simp
  · next hn =>
    rw [if_neg hn, Env.find?_cons]
    split <;> simp_all

/-- Conses of the SAME name over dominating environments dominate. -/
theorem find?_cons_mono {c c' : ConstantInfo} {envA envB : Env} (hn : c.name = c'.name)
    (hf : ∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true) :
    ∀ n, (Env.find? ⟨c :: envA.consts⟩ n).isSome = true →
      (Env.find? ⟨c' :: envB.consts⟩ n).isSome = true := by
  intro n h
  rw [Env.find?_cons] at h
  rw [Env.find?_cons, ← hn]
  split at h
  · next hh => rw [if_pos hh]; simp
  · next hh => rw [if_neg hh]; exact hf n h

/-- The recursors' cons finds everything the environment below it
finds. -/
theorem find?_consBlockRecs_le {find? : Name → Option ConstantInfo} {q : BlockShape} {nP : Nat} :
    ∀ {m : Nat} {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
      {env : Env} (n : Name),
      (env.find? n).isSome = true →
      ((consBlockRecs find? q nP m rs env).find? n).isSome = true
  | _, [], _, _, h => h
  | _, _ :: _, env, n, h => by
    simp only [consBlockRecs]
    refine find?_consBlockRecs_le n ?_
    rw [Env.find?_cons]
    split <;> simp_all

/-- **The bare-`k` environment finds no name the stored one does not**:
`consBlockRecsBare` and `consBlockRecs` cons the same names in the same
order, and resolution reads the environment through its names alone.
This is what carries the new stage's rule scoping — stated at the
environment holding all `k` RULE-LESS recursors — to the environment
the rules are STORED in. -/
theorem find?_consBlockRecs_of_bare {find? : Name → Option ConstantInfo} {q : BlockShape}
    {nP : Nat} :
    ∀ {m : Nat} {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
      {envA envB : Env},
      (∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true) →
      ∀ n, ((consBlockRecsBare q m (rs.map fun r => (r.1, r.2.2.1)) envA).find? n).isSome = true →
        ((consBlockRecs find? q nP m rs envB).find? n).isSome = true
  | _, [], _, _, hf, n, h => hf n h
  | m, (cvRa, rhss, nIdx, ctorsA) :: rest, envA, envB, hf, n, h => by
    simp only [List.map_cons, consBlockRecsBare] at h
    simp only [consBlockRecs]
    refine find?_consBlockRecs_of_bare
      (envA := ⟨.recInfo cvRa (q.majorIdxAt m) (q.rulePrefixAt m) [] :: envA.consts⟩) ?_ n h
    exact find?_cons_mono rfl hf

/-- **What the recursors' cons holds**: the `k` recursor records, each
with its rules, and what was stored below them. -/
theorem mem_consBlockRecs {find? : Name → Option ConstantInfo} {q : BlockShape} {nP : Nat} :
    ∀ {m : Nat} {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
      {env : Env} {c : ConstantInfo},
      c ∈ (consBlockRecs find? q nP m rs env).consts →
      c ∈ env.consts ∨ ∃ r ∈ rs, ∃ j,
        c = .recInfo r.1 (q.majorIdxAt j) (q.rulePrefixAt j)
          (sumRules find? r.1.name nP (q.majorIdxAt j) (q.rulePrefixAt j)
            r.1.type r.2.2.2 r.2.1)
  | _, [], _, _, h => Or.inl h
  | m, r0 :: rest, env, c, h => by
    simp only [consBlockRecs] at h
    rcases mem_consBlockRecs h with h' | ⟨r, hr, j, hj⟩
    · rcases List.mem_cons.mp h' with rfl | h'
      · exact Or.inr ⟨r0, List.mem_cons_self, m, rfl⟩
      · exact Or.inl h'
    · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, j, hj⟩

/-- **The k recursors' cons keeps well-formedness — SIMULTANEOUSLY.**

The `k` rule-carrying records are consed onto one environment and
every one of them is checked against the FINAL one: `EnvWF E` is
`∀ c ∈ E.consts, ConstWF E c`, so nothing forces a per-record
intermediate environment, and nothing could — a rule of `rec_0` may
name `rec_1`, so it resolves only where all `k` recursors stand.  Its
scoping hypothesis is therefore stated at the BARE-`k` environment,
which finds exactly the names the stored cons finds
(`find?_consBlockRecs_of_bare`); the rules themselves are `sumRules`'
per recursor, so `sumRules_mem` is the block's rule fact unchanged. -/
theorem envWF_consBlockRecs {find? : Name → Option ConstantInfo} {q : BlockShape} {nP : Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {env : Env}
    (henv : EnvWF env)
    (hall : ∀ r ∈ rs, r.1.type.hasFvar = false ∧
      r.1.type.allLevelParamsDefined r.1.levelParams = true ∧
      r.1.type.constsResolve env = true ∧
      r.1.type.looseBVarsBounded 0 = true ∧
      ∀ rhs ∈ r.2.1, rhs.hasFvar = false ∧
        rhs.allLevelParamsDefined r.1.levelParams = true ∧
        rhs.constsResolve (consBlockRecsBare q 0 (rs.map fun r => (r.1, r.2.2.1)) env) = true ∧
        rhs.looseBVarsBounded 0 = true) :
    EnvWF (consBlockRecs find? q nP 0 rs env) := by
  have hdomEnv : ∀ n, (env.find? n).isSome = true →
      ((consBlockRecs find? q nP 0 rs env).find? n).isSome = true :=
    fun n hn => find?_consBlockRecs_le n hn
  have hdomBare : ∀ n,
      ((consBlockRecsBare q 0 (rs.map fun r => (r.1, r.2.2.1)) env).find? n).isSome = true →
      ((consBlockRecs find? q nP 0 rs env).find? n).isSome = true :=
    find?_consBlockRecs_of_bare (fun _ hn => hn)
  intro c hc
  rcases mem_consBlockRecs hc with hc' | ⟨r, hr, j, rfl⟩
  · exact ConstWF.mono hdomEnv (henv c hc')
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hall r hr
    refine structConstWF h1 h2 (Expr.constsResolve_le hdomEnv h3) h4
      (fun _ _ _ heq => nomatch heq) ?_
    intro cvR' mI' rP' rules' heq rl hrl
    injection heq with e1 e2 e3 e4
    subst e1
    subst e4
    obtain ⟨hmem, hfire⟩ := sumRules_mem hrl
    obtain ⟨g1, g2, g3, g4⟩ := h5 rl.rhs hmem
    refine ⟨g1, g2, Expr.constsResolve_le hdomBare g3, g4, ?_⟩
    intro lvls pins hf
    exact absurd hf (hfire lvls pins)

/-! ## The literal guards across the recursors' cons

The recursors' cons must not change what a `Nat` or `String` literal
READS.  Both guards decide that by looking fixed names up in the store
(`litGuardNames`), and the stage refuses a recursor under any of them
(`blockRecNamesUnreserved`, inverted as `checkBlockRecPins_reserved`),
so every one of those lookups crosses the cons untouched.

Without the stage's check the `String` guard is only MONOTONE, and
refutably so: `listConsTyOk` asks for a constant `List.cons.{p} :
∀ (α : Type p) (h : α) (t : List.{p} α), List.{p} α`, and a block
declaring `List : Type p → Type p` with a recursor NAMED `List.cons`
of exactly that type would flip `strLitSupported` from `false` to
`true` across its own recursor stage. -/

/-- **A name no recursor of the block carries reads through the cons
unchanged.** -/
theorem find?_consBlockRecs_of_ne {find? : Name → Option ConstantInfo}
    {q : BlockShape} {nP : Nat} {n : Name} :
    ∀ {m : Nat} {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
      {env : Env},
      (∀ r ∈ rs, n ≠ r.1.name) →
      (consBlockRecs find? q nP m rs env).find? n = env.find? n
  | _, [], _, _ => rfl
  | m, r0 :: rest, env, hne => by
    rw [consBlockRecs,
      find?_consBlockRecs_of_ne (fun r hr => hne r (List.mem_cons_of_mem _ hr)),
      Env.find?_cons, if_neg (fun h => hne r0 List.mem_cons_self h.symm)]

/-- A name a literal guard looks up is no recursor of a CHECKED
block. -/
theorem ne_of_reservedRecName
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {n : Name}
    (hnres : ∀ r ∈ rs, reservedRecName r.1.name = false)
    (hn : reservedRecName n = true) : ∀ r ∈ rs, n ≠ r.1.name := by
  intro r hr hh
  rw [hh, hnres r hr] at hn
  exact nomatch hn

/-- **The `Nat`-literal guard is CONGRUENT across the recursors'
cons.** -/
theorem natLitSupported_consBlockRecs {find? : Name → Option ConstantInfo}
    {q : BlockShape} {nP : Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {env : Env}
    (hnres : ∀ r ∈ rs, reservedRecName r.1.name = false) :
    natLitSupported (consBlockRecs find? q nP 0 rs env) = natLitSupported env := by
  unfold natLitSupported
  rw [find?_consBlockRecs_of_ne (ne_of_reservedRecName hnres (by decide)),
    find?_consBlockRecs_of_ne (ne_of_reservedRecName (n := natZeroName) hnres (by decide)),
    find?_consBlockRecs_of_ne (ne_of_reservedRecName (n := natSuccName) hnres (by decide))]

/-- **The `String`-literal guard is CONGRUENT across the recursors'
cons** — the equation the model's reading law needs, and the reason
`blockRecNamesUnreserved` is checked at all. -/
theorem strLitSupported_consBlockRecs {find? : Name → Option ConstantInfo}
    {q : BlockShape} {nP : Nat}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {env : Env}
    (hnres : ∀ r ∈ rs, reservedRecName r.1.name = false) :
    strLitSupported (consBlockRecs find? q nP 0 rs env) = strLitSupported env := by
  unfold strLitSupported
  rw [natLitSupported_consBlockRecs hnres,
    find?_consBlockRecs_of_ne (ne_of_reservedRecName (n := stringName) hnres (by decide)),
    find?_consBlockRecs_of_ne (ne_of_reservedRecName (n := stringOfListName) hnres (by decide)),
    find?_consBlockRecs_of_ne (ne_of_reservedRecName (n := listName) hnres (by decide)),
    find?_consBlockRecs_of_ne (ne_of_reservedRecName (n := listNilName) hnres (by decide)),
    find?_consBlockRecs_of_ne (ne_of_reservedRecName (n := listConsName) hnres (by decide)),
    find?_consBlockRecs_of_ne (ne_of_reservedRecName (n := charName) hnres (by decide)),
    find?_consBlockRecs_of_ne (ne_of_reservedRecName (n := charOfNatName) hnres (by decide))]

/-- **The CHECK's stored recursors take no guarded name** — the stage's
own `blockRecNamesUnreserved`, transported from the RECORDS to the
constants the stage stores (`checkConstantVal` keeps a record's
name). -/
theorem checkBlockRecK_reserved {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRecK (fueledOps mode F) env p cvTas ctorsAs = .ok rs) :
    ∀ r ∈ rs, reservedRecName r.1.name = false := by
  unfold checkBlockRecK at h
  obtain ⟨u, hpins, h⟩ := exceptBind_ok h
  obtain ⟨cvRus, htys, h⟩ := exceptBind_ok h
  obtain ⟨_, _, h⟩ := exceptBind_ok h
  obtain ⟨hlenT, hallT⟩ := checkBlockRecTys_inv htys
  obtain ⟨hlenR, hallR⟩ := checkBlockRecsRules_facts h
  have hres := checkBlockRecPins_reserved (p := p) (by cases u; exact hpins)
  intro r hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  have hil : i < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨rc, r', hrc, hr', hcvRa, -⟩ := hallR i hil
  obtain rfl := Option.some.inj (hi.symm.trans hr')
  obtain ⟨rc'', cvRi, nIdx, u', hrc'', hcu, hcv, -, -⟩ := hallT i hil
  obtain rfl := Option.some.inj (hrc.symm.trans hrc'')
  have hcvRa' : (cvRus.map (fun q => (q.1, q.2.1)))[i]? = some (cvRi, nIdx) := by
    rw [List.getElem?_map, hcu]; rfl
  have hr1 : r.1 = cvRi := by
    have := hcvRa
    rw [Nat.zero_add] at this
    exact congrArg Prod.fst (Option.some.inj (this.symm.trans hcvRa'))
  rw [hr1, (checkConstantVal_lps hcv).1]
  exact hres rc (List.mem_of_getElem? hrc)

/-! ## The projection tables -/

/-- **The tables at the run level**: a table is consed at every
structure-like member and nothing at any other, and either keeps
well-formedness. -/
theorem direct_block_tables_wf {q : BlockShape} :
    ∀ {l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))}
      {env env₂ : Env},
      EnvWF env → checkBlockTables (m := CheckM) q l env = .ok env₂ → EnvWF env₂
  | [], env, env₂, henv, h => by
    simp only [checkBlockTables, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ henv
  | (ms, ctorsA, sortss) :: rest, env, env₂, henv, h => by
    unfold checkBlockTables at h
    obtain ⟨env', henv', h⟩ := exceptBind_ok h
    refine direct_block_tables_wf ?_ h
    revert henv'
    split
    · split
      · intro hh; exact direct_table_wf henv hh
      · intro hh
        simp only [pure, Except.pure, Except.ok.injEq] at hh
        exact hh ▸ henv
    · intro hh
      simp only [pure, Except.pure, Except.ok.injEq] at hh
      exact hh ▸ henv

/-! ## The whole install -/


/-! ## The block's η invariant, established -/

/-- A `Nodup` concatenation of per-element lists has DISJOINT members
at distinct positions (the shape `BlockShape.allCtors` has: the
members' constructor lists, concatenated). -/
private theorem flatten_disjoint_of_nodup {α : Type _} {β : Type _} [DecidableEq β]
    {f : α → List β} :
    ∀ {L : List α}, ((L.map f).flatten).Nodup →
      ∀ {i j : Nat} {a b : α}, i ≠ j → L[i]? = some a → L[j]? = some b →
      ∀ x ∈ f a, ∀ y ∈ f b, x ≠ y
  | [], _, i, _, _, _, _, hi, _ => by simp at hi
  | a₀ :: L, hnd, i, j, a, b, hij, hi, hj => by
    simp only [List.map_cons, List.flatten_cons] at hnd
    obtain ⟨-, hnd', hcross⟩ := List.nodup_append.mp hnd
    have hin : ∀ {q : Nat} {c : α}, L[q]? = some c → ∀ y ∈ f c, y ∈ (L.map f).flatten := by
      intro q c hq y hy
      exact List.mem_flatten.mpr ⟨f c, List.mem_map.mpr ⟨c, List.mem_of_getElem? hq, rfl⟩, hy⟩
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 0, j + 1 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [List.getElem?_cons_succ] at hj
      exact fun x hx y hy => hcross x hx y (hin hj y hy)
    | i + 1, 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [List.getElem?_cons_succ] at hi
      exact fun x hx y hy => fun hh => hcross y hy x (hin hi x hx) hh.symm
    | i + 1, j + 1 =>
      simp only [List.getElem?_cons_succ] at hi hj
      exact flatten_disjoint_of_nodup hnd' (fun hh => hij (by omega)) hi hj

/-- **The constructor names of the block member called `n`** — `[]` off
the block, and at a member its own list (the block's member names are
distinct).  This is `BlockEtaInv`'s `ctorsOf` at a block. -/
def BlockShape.ctorNamesAt (p : BlockShape) (n : Name) : List Name :=
  (p.members.filter (fun ms => ms.cvT.name == n)).flatMap (fun ms => ms.ctors.map (·.1.name))

theorem BlockShape.mem_ctorNamesAt {p : BlockShape} {ms : MemberShape} {c : ConstantVal × Nat}
    (hms : ms ∈ p.members) (hc : c ∈ ms.ctors) : c.1.name ∈ p.ctorNamesAt ms.cvT.name := by
  rw [BlockShape.ctorNamesAt, List.mem_flatMap]
  exact ⟨ms, List.mem_filter.mpr ⟨hms, by simp⟩, List.mem_map.mpr ⟨c, hc, rfl⟩⟩

theorem BlockShape.ctorNamesAt_mem {p : BlockShape} {n n' : Name}
    (h : n' ∈ p.ctorNamesAt n) :
    ∃ ms ∈ p.members, ms.cvT.name = n ∧ ∃ c ∈ ms.ctors, c.1.name = n' := by
  rw [BlockShape.ctorNamesAt, List.mem_flatMap] at h
  obtain ⟨ms, hms, hc⟩ := h
  obtain ⟨hms', hname⟩ := List.mem_filter.mp hms
  obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hc
  exact ⟨ms, hms', by simpa using hname, c, hc', rfl⟩

/-- **A member's η constructor is one of ITS OWN constructors**: the
capability record claims η only where the member has exactly one
constructor, and names that one. -/
theorem blockCapsAt_etaCtor_mem {p₁ : BlockShape} {isRec : Bool} {j : Nat} {ms : MemberShape}
    (hms : p₁.members[j]? = some ms) (he : (blockCapsAt p₁ j isRec).eta = true) :
    (blockCapsAt p₁ j isRec).etaCtor ∈ p₁.ctorNamesAt ms.cvT.name := by
  have hgetD : p₁.members.getD j default = ms := by
    rw [List.getD_eq_getElem?_getD, hms, Option.getD_some]
  match hcs : ms.ctors with
  | [c] =>
    have : (blockCapsAt p₁ j isRec).etaCtor = c.1.name := by
      rw [blockCapsAt, hgetD, hcs]
    rw [this]
    exact BlockShape.mem_ctorNamesAt (List.mem_of_getElem? hms) (by rw [hcs]; exact List.mem_cons_self)
  | [] => rw [blockCapsAt, hgetD, hcs] at he; exact nomatch he
  | c :: c' :: cs => rw [blockCapsAt, hgetD, hcs] at he; exact nomatch he

/-- **A `.indInfo` found after the `k` formers' conses** is one of them,
with ITS capability record, or was stored before the block. -/
theorem find?_consBlockInds_indInfo {p₁ : BlockShape} {isRec : Bool} :
    ∀ {cvTas : List ConstantVal} {i : Nat} {env : Env} {T' : Name}
      {cvT : ConstantVal} {caps : IndCaps},
      (consBlockInds p₁ isRec cvTas i env).find? T' = some (.indInfo cvT caps) →
      (∃ j, cvTas[j]? = some cvT ∧ cvT.name = T' ∧ caps = blockCapsAt p₁ (i + j) isRec) ∨
      env.find? T' = some (.indInfo cvT caps)
  | [], _, _, _, _, _, h => Or.inr h
  | cvTa :: rest, i, env, T', cvT, caps, h => by
    simp only [consBlockInds] at h
    rcases find?_consBlockInds_indInfo h with ⟨j, hj, hname, hcaps⟩ | h'
    · exact Or.inl ⟨j + 1, hj, hname, by rw [hcaps, show i + 1 + j = i + (j + 1) from by omega]⟩
    · rw [ConLeche.Env.find?_cons] at h'
      split at h'
      · next heq =>
        obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj h')
        exact Or.inl ⟨0, rfl, heq, by rw [Nat.add_zero]⟩
      · exact Or.inr h'

/-- **`BlockEtaInv`'s second conjunct at the `k` formers' cons**: every
stored member's η constructor is one of that member's own constructors.
The members' names are fresh before the block, so a stored `.indInfo`
at a member's name IS that member's cons. -/
theorem blockEtaInv_snd_consBlockInds {p₁ : BlockShape} {isRec : Bool}
    {cvTas : List ConstantVal} {env : Env} {names : List Name}
    (hfresh : ∀ T' ∈ names, env.find? T' = none)
    (hms : ∀ (j : Nat) (cvTa : ConstantVal), cvTas[j]? = some cvTa →
      ∃ ms, p₁.members[j]? = some ms ∧ ms.cvT.name = cvTa.name) :
    ∀ (T' : Name) (cvT : ConstantVal) (caps : IndCaps),
      (consBlockInds p₁ isRec cvTas 0 env).find? T' = some (.indInfo cvT caps) →
      T' ∈ names → caps.eta = true → caps.etaCtor ∈ p₁.ctorNamesAt T' := by
  intro T' cvT caps hf hmem hcape
  rcases find?_consBlockInds_indInfo hf with ⟨j, hj, rfl, rfl⟩ | h'
  · obtain ⟨ms, hmsj, hname⟩ := hms j cvT hj
    rw [Nat.zero_add] at hcape ⊢
    rw [← hname]
    exact blockCapsAt_etaCtor_mem hmsj hcape
  · rw [hfresh T' hmem] at h'; exact nomatch h'

/-- **A member's constructor completes no OTHER member's η family.**
The block's constructor names are distinct (`DeclBlockRun`'s conjunct
0) and `allCtors` is the members' lists concatenated, so distinct
members' constructor names are disjoint; `BlockEtaInv.other`'s `hout`
is that disjointness at the member being consed. -/
theorem blockCtorNames_out {p₁ : BlockShape}
    (hnd : (p₁.allCtors.map (·.1.name)).Nodup)
    {m : Nat} {msm : MemberShape} (hm : p₁.members[m]? = some msm)
    {n : Name} (hn : n ∈ msm.ctors.map (·.1.name))
    (T'' : Name) (_hT : T'' ∈ p₁.memberNames) (hne : T'' ≠ msm.cvT.name) :
    n ∉ p₁.ctorNamesAt T'' := by
  intro hmem
  obtain ⟨ms, hms, hmsn, c, hc, hcn⟩ := BlockShape.ctorNamesAt_mem hmem
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hms
  have hjm : j ≠ m := by
    intro hh
    subst hh
    obtain rfl : ms = msm := Option.some.inj (hj.symm.trans hm)
    exact hne hmsn.symm
  have hflat : ((p₁.members.map (fun ms => ms.ctors.map (·.1.name))).flatten).Nodup := by
    have : p₁.allCtors.map (·.1.name)
        = (p₁.members.map (fun ms => ms.ctors.map (·.1.name))).flatten := by
      rw [BlockShape.allCtors, List.map_flatten, List.map_map]
      rfl
    rwa [this] at hnd
  exact flatten_disjoint_of_nodup hflat hjm hj hm c.1.name
    (List.mem_map.mpr ⟨c, hc, rfl⟩) n hn hcn

/-- **`EnvWF` through the whole uniform install**: the k formers, the
N constructors, the k recursors with their rules, and the projection
tables. -/
theorem direct_block_wf {env env₂ : Env} (henv : EnvWF env)
    {p₀ : BlockParts} {isRec b : Bool} {q : BlockPass Env} {F : Nat}
    (hP : checkBlockPass (fueledOps mode F) env p₀ isRec = .ok (q, b))
    (h : checkBlockTail (m := CheckM) (fueledOps mode F) env q = .ok env₂) :
    EnvWF env₂ := by
  obtain ⟨p₁, kinds, hInd, hCtors, -, hp, -⟩ := checkBlockPass_inv hP
  obtain ⟨isorts, rs, -, -, -, hRec, hTbl⟩ := checkBlockTail_inv h
  have h1 : EnvWF q.env₁ := (direct_block_inds_wf henv hInd).1
  have h2 : EnvWF (consBlockCtors q.p.nP q.ctorsAs q.env₁) :=
    direct_block_ctors_wf h1 hCtors
  have h3 : EnvWF (consBlockRecs (consBlockCtors q.p.nP q.ctorsAs q.env₁).find?
      q.p.toBlockShape q.p.nP 0 rs (consBlockCtors q.p.nP q.ctorsAs q.env₁)) :=
    envWF_consBlockRecs h2 (checkBlockRec_facts hRec)
  exact direct_block_tables_wf h3 hTbl

/-! ## The family's shared rule PREFIX (the ruling of 2026-09-22)

Stage (b') compares every recursor's opened rule prefix with the FIRST
one's, binder by binder, up to defeq.  What the model needs of it is
the per-position `isDefEq`, at the two openings — the fact that lets
it identify the classes' prefix domains and so put a guarded call's
predecessor in the CALLEE's class (the lane's `hpref'`). -/

/-- **`checkBlockDefEqList`, inverted**: the lists have the same length
and every position is defeq at the stage's depth. -/
theorem checkBlockDefEqList_inv {env : Env} {F depth : Nat} {what : String} :
    ∀ {as bs : List Expr},
      checkBlockDefEqList (fueledOps mode F) env depth what as bs = .ok () →
      as.length = bs.length ∧
      ∀ l, l < as.length →
        isDefEqCore mode env F depth (as.getD l default) (bs.getD l default) = .ok true
  | [], [], _ => ⟨rfl, fun l hl => absurd hl (Nat.not_lt_zero l)⟩
  | [], _ :: _, h => by
    simp only [checkBlockDefEqList, throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  | _ :: _, [], h => by
    simp only [checkBlockDefEqList, throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  | a :: as, b :: bs, h => by
    rw [checkBlockDefEqList] at h
    simp only [fueledOps_isDefEq] at h
    obtain ⟨c, hc, h⟩ := exceptBind_ok h
    by_cases hcb : c = true
    case neg =>
      rw [Bool.not_eq_true] at hcb
      subst hcb
      simp only [Bool.false_eq_true, if_false, throw, throwThe, MonadExceptOf.throw,
        Bind.bind, Except.bind] at h
      exact nomatch h
    subst hcb
    simp only [if_pos, Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨hlen, hall⟩ := checkBlockDefEqList_inv h
    refine ⟨by simp [hlen], fun l hl => ?_⟩
    cases l with
    | zero => simpa using hc
    | succ l => simpa using hall l (by simpa using hl)

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
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
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

/-! ## Stage (b)'s PARAMETER CHAIN (the comparison `checkBlockRecTys_inv`
discards)

`checkBlockRecTys` compares the recursor's first `nP` binder domains,
binder by binder at the block's parameter depth, with the MEMBER'S OWN
type former's opened parameter telescope (`checkBlockDefEqList` at
`p.nP`).  `checkBlockRecTys_inv` peels that bind positionally and
throws the result away — and so does every inversion built on it — so
the model tier cannot see the one fact that ties the rule frame's
parameter values to the CONSTRUCTOR's domains (whose own comparison is
against the same former, `checkSumCtor`'s `checkStructDomsAt`).

This is a SEPARATE re-inversion in the style of
`checkBlockRecPrefixAt_inv` rather than a widening of
`checkBlockRecTys_inv`: the latter is peeled positionally in five
modules, two of them other lanes'.  The comparison runs at the FIXED
depth `p.nP` (not per binder), which is `prefixDoms_spineFit`'s shape
— the certified hop was written for exactly this kind of stage. -/

/-- **Stage (b)'s parameter chain, inverted**: recursor `i`'s stored
type opens, its member's type former opens at the block's parameter
count, and the two openings' domains are defeq position by position at
depth `p.nP`. -/
theorem checkBlockRecTys_params {env : Env} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {F : Nat} :
    ∀ {recs : List RecShape} {ri : Nat} {cvRus : List (ConstantVal × Nat × Level)},
      checkBlockRecTys (fueledOps mode F) env p nested cvTas recs ri = .ok cvRus →
      ∀ i, i < recs.length →
        ∃ (cvRi cvTa : ConstantVal) (nIdx : Nat) (u : Level)
          (tfvs fvs : List Expr) (trest concl : Expr),
          cvRus[i]? = some (cvRi, nIdx, u) ∧
          cvTas[p.recTgtAt (ri + i)]? = some cvTa ∧
          openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest) ∧
          openPisAtFvars (p.majorIdxAt (ri + i) + 1) cvRi.type 0 = some (fvs, concl) ∧
          tfvs.length = (fvs.take p.nP).length ∧
          ∀ l, l < tfvs.length →
            isDefEqCore mode env F p.nP ((tfvs.map Expr.fvarTypeD).getD l default)
              (((fvs.take p.nP).map Expr.fvarTypeD).getD l default) = .ok true
  | [], _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | rc :: rest, ri, cvRus, h, i, hi => by
    unfold checkBlockRecTys at h
    obtain ⟨ms, _, h⟩ := exceptBind_ok h
    obtain ⟨cvTa, hcvTa, h⟩ := exceptBind_ok h
    obtain ⟨cvRi, _, h⟩ := exceptBind_ok h
    by_cases hle : p.nP ≤ p.rulePrefixAt ri
    case neg => rw [if_neg hle] at h; close_throw h
    rw [if_pos hle] at h
    by_cases hle2 : (p.majorIdxAt ri == p.rulePrefixAt ri + ms.nIdx) = true
    case neg => rw [if_neg hle2] at h; close_throw h
    rw [if_pos hle2] at h
    obtain ⟨x1, hx1, h⟩ := exceptBind_ok h
    obtain ⟨fvs, concl⟩ := x1
    have hop : openPisAtFvars (p.majorIdxAt ri + 1) cvRi.type 0 = some (fvs, concl) :=
      unwrapOr_ok hx1
    obtain ⟨x2, hx2, h⟩ := exceptBind_ok h
    obtain ⟨tfvs, trest⟩ := x2
    have hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest) := unwrapOr_ok hx2
    obtain ⟨ud, hud, h⟩ := exceptBind_ok h
    obtain ⟨hlenD, hallD⟩ := checkBlockDefEqList_inv
      (what := s!"the recursor {rc.cvR.name}'s parameter domains are not the block's")
      (by cases ud; exact hud)
    simp only [List.length_map] at hlenD hallD
    obtain ⟨maj, _, h⟩ := exceptBind_ok h
    by_cases hmaj : (maj.fvarTypeD.getAppFn == Expr.const ms.cvT.name (p.lps.map .param) &&
        maj.fvarTypeD.getAppArgs.length == p.nP + ms.nIdx &&
        maj.fvarTypeD.getAppArgs.take p.nP == fvs.take p.nP &&
        maj.fvarTypeD.getAppArgs.drop p.nP ==
          (fvs.drop (p.rulePrefixAt ri)).take ms.nIdx) = true
    case neg => rw [if_neg hmaj] at h; close_throw h
    rw [if_pos hmaj] at h
    obtain ⟨sty, _, h⟩ := exceptBind_ok h
    obtain ⟨u, _, h⟩ := exceptBind_ok h
    have key : ∀ {rs' : List (ConstantVal × Nat × Level)},
        checkBlockRecTys (fueledOps mode F) env p nested cvTas rest (ri + 1) = .ok rs' →
        cvRus = (cvRi, ms.nIdx, u) :: rs' →
        ∃ (cvRi' cvTa' : ConstantVal) (nIdx : Nat) (u' : Level)
          (tfvs' fvs' : List Expr) (trest' concl' : Expr),
          cvRus[i]? = some (cvRi', nIdx, u') ∧
          cvTas[p.recTgtAt (ri + i)]? = some cvTa' ∧
          openPisAtFvars p.nP cvTa'.type 0 = some (tfvs', trest') ∧
          openPisAtFvars (p.majorIdxAt (ri + i) + 1) cvRi'.type 0 = some (fvs', concl') ∧
          tfvs'.length = (fvs'.take p.nP).length ∧
          ∀ l, l < tfvs'.length →
            isDefEqCore mode env F p.nP ((tfvs'.map Expr.fvarTypeD).getD l default)
              (((fvs'.take p.nP).map Expr.fvarTypeD).getD l default) = .ok true := by
      intro rs' hrest hcv
      subst hcv
      cases i with
      | zero =>
        exact ⟨cvRi, cvTa, ms.nIdx, u, tfvs, fvs, trest, concl, rfl,
          by simpa using unwrapOr_ok hcvTa, by simpa using hopT, by simpa using hop,
          by simpa using hlenD, by simpa using hallD⟩
      | succ i =>
        obtain ⟨cvRi', cvTa', nIdx, u', tfvs', fvs', trest', concl', hcu, hcvT, hopT',
          hop', hlenD', hallD'⟩ := checkBlockRecTys_params hrest i (by simpa using hi)
        refine ⟨cvRi', cvTa', nIdx, u', tfvs', fvs', trest', concl', by simpa using hcu, ?_, hopT',
          ?_, hlenD', hallD'⟩
        · rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hcvT
        · rw [show ri + (i + 1) = ri + 1 + i from by omega]; exact hop'
    by_cases hlarge : blockLargeElimAllowed p nested = true
    case pos =>
      rw [if_pos hlarge] at h
      obtain ⟨rs', hrest, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact key hrest h.symm
    case neg =>
      rw [if_neg hlarge] at h
      obtain ⟨b, _, h⟩ := exceptBind_ok h
      by_cases hb : b = true
      case neg => rw [if_neg hb] at h; close_throw h
      rw [if_pos hb] at h
      obtain ⟨rs', hrest, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact key hrest h.symm

end ConLeche
