module

public import ConLeche.Verify.Inductives.SumInv
import ConLeche.Verify.Inductives.FixParts
import ConLeche.Kernel.Inductives.BlockTail

public section

/-!
# The uniform install's stage runs, inverted at k members
(the uniform inductive route, milestone M4)

Each stage of `checkBlock` (`ConLeche/Kernel/Inductives/BlockInstall.lean`)
read back as the facts the semantic and model tiers consume — the
k-ary twins of `FixInv.lean` (`classifyFixKinds_inv`,
`checkNativePass_inv`) and `SumInv.lean` (`checkSumInd_shape`,
`checkSumCtors_inv`), which stay the PER-MEMBER stages the block's
loops call:

* **the formers** (`checkBlockTele_shape`, `checkBlockTeles_inv`,
  `checkBlockDomsAt_inv`, `checkBlockAgree_inv`,
  `checkBlockInds_shape`): the constant check and official's telescope
  loop per member, then — from member 1 on — official's two agreements
  (the parameter domains definitionally member 0's, the result sorts
  `Level.isEquiv`), and the k formers consed at once
  (`consBlockInds`), which is the environment every constructor is
  checked at;
* **the constructors** (`checkBlockCtors_inv`): `checkSumCtors` at
  every member, at that environment;
* **the kinds** (`classifyMemberKinds_inv`, `classifyBlockKinds_inv`)
  against the WHOLE member list;
* **the tail** (`checkBlockIdxSorts_inv`, `blockOpenedOk_inv`,
  `blockFieldsOk_inv`, `checkBlockTail_inv`), and the TARGET BOUND read
  off the re-check (`blockOpenedOk_tgt_lt`,
  `blockMemberFieldsOk_tgtsOf_lt`): every target a kind carries is a
  member of the block because the re-check says so, not because the
  classifier's arms produce only members (lane NESTPOS, ARCH R2(b) —
  the positivity walk has no proof consumer)
  and **the pass** (`checkBlockPass_inv`).

The recursor stage stays OPAQUE here — `checkBlockTail_inv` exposes it
as `checkBlockRec … = .ok rs` — so that milestone M5's replacement of
the whole stage (`checkBlockRec_inv`, the `abstractIh` spec) fits
without restating the tail.
-/

-- the `simp only` sets below are written for robustness against the
-- normal forms of the two sides, and several entries fire on one side only
set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

private theorem bThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact bThrow_ne_ok (by assumption))
        | (exfalso; exact bThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-! ## Stage 1: the members' type formers -/

/-- One member's former, inverted: `checkSumInd_shape` without the
environment cons — at k members nothing is consed before every former
has been checked (official's `declare_inductive_types`). -/
theorem checkBlockTele_shape {env : Env} {nP : Nat} {ms : MemberShape}
    {cvTa : ConstantVal} {s : Level} {F : Nat}
    (h : checkBlockTele (fueledOps mode F) env nP ms = .ok (cvTa, s)) :
    ∃ cvT : ConstantVal,
      cvT.name = ms.cvT.name ∧ cvT.levelParams = ms.cvT.levelParams ∧
      checkConstantVal (fueledOps mode F) env cvT = .ok cvTa ∧
      ∃ bs, cvTa.type.stripPis (nP + ms.nIdx) = some (bs, .sort s) := by
  unfold checkBlockTele at h
  obtain ⟨cvTa₀, hccv₀, h⟩ := exceptBind_ok h
  obtain ⟨q, htele, h⟩ := exceptBind_ok h
  obtain ⟨cvTa', s'⟩ := q
  try simp only at h
  obtain ⟨r, hr, h⟩ := exceptBind_ok h
  obtain ⟨bs, tbody⟩ := r
  have hr' := unwrapOr_ok hr
  try simp only at h
  by_cases hc : (tbody == Expr.sort s') = true
  · rw [if_pos hc] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hstrip : cvTa'.type.stripPis (nP + ms.nIdx) = some (bs, Expr.sort s') := by
      rw [hr', beq_iff_eq.mp hc]
    rcases checkSumTele_shape htele with ⟨rfl, -⟩ | ⟨ty, hccv⟩
    · exact ⟨ms.cvT, rfl, rfl, hccv₀, bs, hstrip⟩
    · exact ⟨{ ms.cvT with type := ty }, rfl, rfl, hccv, bs, hstrip⟩
  · rw [if_neg hc] at h
    close_throw

/-- The members' formers, positionally. -/
theorem checkBlockTeles_inv {env : Env} {nP : Nat} {F : Nat} :
    ∀ {mss : List MemberShape} {cvs : List (ConstantVal × Level)},
      checkBlockTeles (fueledOps mode F) env nP mss = .ok cvs →
      cvs.length = mss.length ∧
      ∀ (i : Nat) (ms : MemberShape), mss[i]? = some ms →
        ∃ q, cvs[i]? = some q ∧ checkBlockTele (fueledOps mode F) env nP ms = .ok q
  | [], cvs, h => by
    simp only [checkBlockTeles, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i ms hms => by simp at hms⟩
  | ms :: rest, cvs, h => by
    unfold checkBlockTeles at h
    obtain ⟨q, hq, h⟩ := exceptBind_ok h
    try simp only at h
    obtain ⟨qs, hqs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := checkBlockTeles_inv hqs
    refine ⟨by simp [hlen], ?_⟩
    intro i ms' hms'
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hms'
      subst hms'
      exact ⟨q, rfl, hq⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hms' ⊢
      exact hall i ms' hms'

/-- The parameter-domain agreement, positionally: every one of the
`nP` domains is definitionally member 0's. -/
theorem checkBlockDomsAt_inv {env : Env} {off : Nat} {fvs doms : List Expr} {F : Nat} :
    ∀ {j : Nat}, checkBlockDomsAt (fueledOps mode F) env off fvs doms j = .ok () →
      ∀ i, i < j → ∃ a b, fvs[i]? = some a ∧ doms[i]? = some b ∧
        isDefEqCore mode env F (off + i) (Expr.fvarTypeD a) b = .ok true
  | 0, _ => fun i hi => absurd hi (Nat.not_lt_zero i)
  | j + 1, h => by
    unfold checkBlockDomsAt at h
    obtain ⟨a, ha, h⟩ := exceptBind_ok h
    have ha' := unwrapOr_ok ha
    try simp only at h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    have hb' := unwrapOr_ok hb
    try simp only at h
    obtain ⟨bb, hbb, h⟩ := exceptBind_ok h
    cases bb with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      close_throw
    | true =>
    rw [if_pos rfl] at h
    try simp only at h
    intro i hi
    rcases Nat.lt_or_ge i j with hij | hij
    · exact checkBlockDomsAt_inv h i hij
    · obtain rfl : i = j := by omega
      exact ⟨a, b, ha', hb', hbb⟩

/-- **Official's two agreements between the members**, inverted: every
member from 1 on opens to as many parameter binders as member 0, each
definitionally member 0's, and carries a result sort `Level.isEquiv` to
member 0's. -/
theorem checkBlockAgree_inv {env : Env} {nP : Nat} {cvTa0 : ConstantVal} {s0 : Level}
    {F : Nat} :
    ∀ {cvs : List (ConstantVal × Level)},
      checkBlockAgree (fueledOps mode F) env nP cvTa0 s0 cvs = .ok () →
      ∀ q ∈ cvs, (Level.isEquiv q.2 s0 == some true) = true ∧
        ∃ tfvs0 trest0 tfvs trest,
          openPisAtFvars nP cvTa0.type 0 = some (tfvs0, trest0) ∧
          openPisAtFvars nP q.1.type 0 = some (tfvs, trest) ∧
          tfvs.length = tfvs0.length ∧
          checkBlockDomsAt (fueledOps mode F) env 0 tfvs
            (tfvs0.map Expr.fvarTypeD) nP = .ok ()
  | [], _ => fun q hq => by simp at hq
  | (cvTa, s) :: rest, h => by
    unfold checkBlockAgree at h
    obtain ⟨q0, hq0, h⟩ := exceptBind_ok h
    have hq0' := unwrapOr_ok hq0
    obtain ⟨tfvs0, trest0⟩ := q0
    try simp only at h
    obtain ⟨q1, hq1, h⟩ := exceptBind_ok h
    have hq1' := unwrapOr_ok hq1
    obtain ⟨tfvs, trest⟩ := q1
    try simp only at h
    by_cases hl : (tfvs.length == tfvs0.length) = true
    case neg => rw [if_neg hl] at h; close_throw
    rw [if_pos hl] at h
    try simp only at h
    obtain ⟨u, hdoms, h⟩ := exceptBind_ok h
    try simp only at h
    by_cases hs : (Level.isEquiv s s0 == some true) = true
    case neg => rw [if_neg hs] at h; close_throw
    rw [if_pos hs] at h
    try simp only at h
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨hs, tfvs0, trest0, tfvs, trest, hq0', hq1', beq_iff_eq.mp hl,
        by cases u; exact hdoms⟩
    · exact checkBlockAgree_inv h q hq

/-- **Stage 1's shape**: member 0's former, the rest of the members'
formers, official's two agreements against member 0, the record
completed with member 0's result sort, and the k formers consed at
once — the environment every constructor is then checked at. -/
theorem checkBlockInds_shape {env envI : Env} {p : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, cvTas, p₁)) :
    ∃ (ms0 : MemberShape) (rest : List MemberShape) (cvTa0 : ConstantVal) (s0 : Level)
      (cvs : List (ConstantVal × Level)),
      p.members = ms0 :: rest ∧
      cvTas = cvTa0 :: cvs.map (·.1) ∧
      p₁ = p.toBlockShape.withSort s0 ∧
      envI = consBlockInds p₁ isRec cvTas 0 env ∧
      checkBlockTele (fueledOps mode F) env p.nP ms0 = .ok (cvTa0, s0) ∧
      checkBlockTeles (fueledOps mode F) env p.nP rest = .ok cvs ∧
      checkBlockAgree (fueledOps mode F) env p.nP cvTa0 s0 cvs = .ok () := by
  unfold checkBlockInds at h
  cases hm : p.members with
  | nil => rw [hm] at h; close_throw
  | cons ms0 rest =>
  rw [hm] at h
  try simp only at h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cvTa0, s0⟩ := q
  try simp only at h
  obtain ⟨cvs, hcvs, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨u, hagree, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨ms0, rest, cvTa0, s0, cvs, rfl, rfl, rfl, rfl, hq, hcvs, by cases u; exact hagree⟩

/-- The annotated formers are one per member. -/
theorem checkBlockInds_length {env envI : Env} {p : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {F : Nat}
    (h : checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, cvTas, p₁)) :
    cvTas.length = p.k := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, rfl, -, -, -, hcvs, -⟩ := checkBlockInds_shape h
  obtain ⟨hlen, -⟩ := checkBlockTeles_inv hcvs
  simp [BlockShape.k, hm, hlen]

/-! ## Stage 1b: the constructors, per member -/

/-- **Every member's constructors**, positionally: the sum route's
constructor loop at the member's own name and index count, at the
BLOCK's level parameters, parameter count, result sort and
elimination data (deviation D-e of milestone M1: official's
`Level.isEquiv` agreement makes the universe bound and the
subsingleton criterion the same test for every member). -/
theorem checkBlockCtors_inv {env₀ env : Env} {q : BlockShape} {ctx : NestCtx} {F : Nat} :
    ∀ {l : List (MemberShape × ConstantVal)} {ctorsAs : List (List (ConstantVal × Nat))}
      {sortsss : List (List (List Level))},
      checkBlockCtors (fueledOps mode F) env₀ env q ctx l = .ok (ctorsAs, sortsss) →
      ctorsAs.length = l.length ∧ sortsss.length = l.length ∧
      ∀ (i : Nat) (mc : MemberShape × ConstantVal), l[i]? = some mc →
        ∃ ctorsA sortss, ctorsAs[i]? = some ctorsA ∧ sortsss[i]? = some sortss ∧
          checkSumCtors (fueledOps mode F) env₀ env ctx mc.1.cvT.name q.lps q.nP mc.1.nIdx
            q.resSort q.isProp q.large mc.2 mc.1.ctors = .ok (ctorsA, sortss)
  | [], ctorsAs, sortsss, h => by
    simp only [checkBlockCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, fun i mc hmc => by simp at hmc⟩
  | (ms, cvTa) :: rest, ctorsAs, sortsss, h => by
    unfold checkBlockCtors at h
    obtain ⟨r, hr, h⟩ := exceptBind_ok h
    obtain ⟨ctorsA, sortss⟩ := r
    try simp only at h
    obtain ⟨r', hr', h⟩ := exceptBind_ok h
    obtain ⟨restC, restS⟩ := r'
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hlen, hlenS, hall⟩ := checkBlockCtors_inv hr'
    refine ⟨by simp [hlen], by simp [hlenS], ?_⟩
    intro i mc hmc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hmc
      subst hmc
      exact ⟨ctorsA, sortss, rfl, rfl, hr⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hmc ⊢
      exact hall i mc hmc

/-! ## The kinds -/

/-- One member's kinds, classified at install (`classifyFixKinds_inv`
at the member list): the recogniser's syntactic reading of the stored
constructors, with no non-positive and no unmodeled occurrence. -/
theorem classifyMemberKinds_inv {names lps : List Name} {nP : Nat} {nIdxs : List Nat}
    {ctorsA : List (ConstantVal × Nat)} {kss : List (List BlockFieldKind)}
    (h : classifyMemberKinds (m := CheckM) names lps nP nIdxs ctorsA = .ok kss) :
    ctorsA.mapM (blockCtorKinds names lps nP nIdxs) = some kss ∧
    kss.any (fun ks => ks.any (· == .negative)) = false ∧
    kss.any (fun ks => ks.any (· == .unsupported)) = false ∧
    kss.length = ctorsA.length := by
  unfold classifyMemberKinds at h
  cases hk : ctorsA.mapM (blockCtorKinds names lps nP nIdxs) with
  | none => rw [hk] at h; exact nomatch h
  | some ks =>
  rw [hk] at h
  simp only [unwrapOr, bind, Except.bind, pure, Except.pure] at h
  by_cases hneg : ks.any (fun ks => ks.any (· == .negative)) = true
  · rw [if_pos hneg] at h; exact nomatch h
  rw [if_neg hneg] at h
  by_cases hun : ks.any (fun ks => ks.any (· == .unsupported)) = true
  · rw [if_pos hun] at h; exact nomatch h
  rw [if_neg hun] at h
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨rfl, by simpa using hneg, by simpa using hun, List.mapM_option_length hk⟩

/-- The kinds of every member, positionally. -/
theorem classifyBlockKinds_inv {names lps : List Name} {nP : Nat} {nIdxs : List Nat} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))}
      {kinds : List (List (List BlockFieldKind))},
      classifyBlockKinds (m := CheckM) names lps nP nIdxs ctorsAs = .ok kinds →
      kinds.length = ctorsAs.length ∧
      ∀ (i : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[i]? = some ctorsA →
        ∃ kss, kinds[i]? = some kss ∧
          classifyMemberKinds (m := CheckM) names lps nP nIdxs ctorsA = .ok kss
  | [], kinds, h => by
    simp only [classifyBlockKinds, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i c hc => by simp at hc⟩
  | ctorsA :: rest, kinds, h => by
    unfold classifyBlockKinds at h
    obtain ⟨kss, hkss, h⟩ := exceptBind_ok h
    try simp only at h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := classifyBlockKinds_inv hrest
    refine ⟨by simp [hlen], ?_⟩
    intro i c hc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨kss, rfl, hkss⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact hall i c hc

/-! ## The pass -/

/-- **One pass's shape at k members** (`checkNativePass_inv` at the
member list): the k formers' run at the record at the verdict `isRec`,
the constructors' runs per member at the environment holding ALL the
formers, the kinds classified on the stored constructors against the
whole member list, the record completed with them, and the settling
bit — the classified record against the one the pass ran at, at every
member. -/
theorem checkBlockPass_inv {env : Env} {p₀ : BlockParts} {isRec : Bool}
    {q : BlockPass Env} {b : Bool} {F : Nat}
    (h : checkBlockPass (fueledOps mode F) env p₀ isRec = .ok (q, b)) :
    ∃ (p₁ : BlockShape) (kinds : List (List (List BlockFieldKind))),
      checkBlockInds (fueledOps mode F) env p₀ isRec = .ok (q.env₁, q.cvTas, p₁) ∧
      (∃ ctx, blockNestCtxOf (p₀.complete p₁).toBlockShape q.cvTas q.env₁.find? q.env₁.consts
          = some ctx ∧
        checkBlockCtors (fueledOps mode F) q.env₁ q.env₁ (p₀.complete p₁).toBlockShape ctx
          ((p₀.complete p₁).members.zip q.cvTas) = .ok (q.ctorsAs, q.sortsss)) ∧
      classifyBlockKinds (m := CheckM) (p₀.complete p₁).memberNames (p₀.complete p₁).lps
        (p₀.complete p₁).nP (p₀.complete p₁).nIdxs q.ctorsAs = .ok kinds ∧
      q.p = (p₀.complete p₁).withKinds kinds ∧
      b = ((List.range q.p.k).all fun i => blockCaps q.p i == blockCapsAt p₁ i isRec) := by
  unfold checkBlockPass at h
  obtain ⟨r₁, hInd, h⟩ := exceptBind_ok h
  obtain ⟨env₁, cvTas, p₁⟩ := r₁
  try simp only at h
  obtain ⟨ctx, hctx, h⟩ := exceptBind_ok h
  obtain ⟨r₂, hCtors, h⟩ := exceptBind_ok h
  obtain ⟨ctorsAs, sortsss⟩ := r₂
  try simp only at h
  obtain ⟨kinds, hK, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨p₁, kinds, hInd, ⟨ctx, unwrapOr_ok hctx, hCtors⟩, hK, rfl, rfl⟩

/-! ## Stage 2: the tail -/

/-- Every member's index binders' sorts, positionally. -/
theorem checkBlockIdxSorts_inv {env₁ : Env} {q : BlockShape} {F : Nat} :
    ∀ {l : List (MemberShape × ConstantVal)} {isorts : List (List Level)},
      checkBlockIdxSorts (fueledOps mode F) env₁ q l = .ok isorts →
      isorts.length = l.length ∧
      ∀ (i : Nat) (mc : MemberShape × ConstantVal), l[i]? = some mc →
        ∃ is tfvs trest, isorts[i]? = some is ∧
          openPisAtFvars (q.nP + mc.1.nIdx) mc.2.type 0 = some (tfvs, trest) ∧
          checkStructFieldSortsI (fueledOps mode F) env₁ true false q.resSort q.nP
            (tfvs.drop q.nP) [] mc.1.nIdx = .ok is
  | [], isorts, h => by
    simp only [checkBlockIdxSorts, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i mc hmc => by simp at hmc⟩
  | (ms, cvTa) :: rest, isorts, h => by
    unfold checkBlockIdxSorts at h
    obtain ⟨tq, htq, h⟩ := exceptBind_ok h
    have htq' := unwrapOr_ok htq
    obtain ⟨tfvs, trest⟩ := tq
    try simp only at h
    obtain ⟨is, his, h⟩ := exceptBind_ok h
    try simp only at h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := checkBlockIdxSorts_inv hrest
    refine ⟨by simp [hlen], ?_⟩
    intro i mc hmc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hmc
      subst hmc
      exact ⟨is, tfvs, trest, rfl, htq', his⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hmc ⊢
      exact hall i mc hmc

/-! ## The field-kinds re-check -/

/-- The field-kinds guard at one member (`nativeFieldsOk_inv` at a
member): the kind list has one entry per field and the opened form
passes the guard, at the TARGET each kind carries. -/
theorem blockMemberFieldsOk_inv {env₀ : Env} {names lps : List Name} {nP : Nat}
    {nIdxs : List Nat} {ctorsA : List (ConstantVal × Nat)}
    {kinds : List (List BlockFieldKind)}
    (h : blockMemberFieldsOk env₀ names lps nP nIdxs ctorsA kinds = true)
    {j : Nat} {cA : ConstantVal × Nat} (hj : ctorsA[j]? = some cA) :
    ∃ ks, kinds[j]? = some ks ∧ ks.length = cA.2 ∧
      blockOpenedOk env₀ names lps nP nIdxs cA.1.type cA.2 ks = true := by
  simp only [blockMemberFieldsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨hlen, hall⟩ := h
  have hjl : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have := hall j hjl
  rw [hj] at this
  cases hk : kinds[j]? with
  | none => rw [hk] at this; exact nomatch this
  | some ks =>
    rw [hk] at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨ks, rfl, this.1, this.2⟩

/-- **The field-kinds guard at k members**: one kind list per member,
and at each member the per-constructor reading above. -/
theorem blockFieldsOk_inv {env₀ : Env} {names lps : List Name} {nP : Nat}
    {nIdxs : List Nat} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List BlockFieldKind))}
    (h : blockFieldsOk env₀ names lps nP nIdxs ctorsAs kinds = true) :
    kinds.length = ctorsAs.length ∧
    ∀ (mi : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[mi]? = some ctorsA →
      ∃ kss, kinds[mi]? = some kss ∧
        blockMemberFieldsOk env₀ names lps nP nIdxs ctorsA kss = true := by
  simp only [blockFieldsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨hlen, hall⟩ := h
  refine ⟨hlen.symm, ?_⟩
  intro mi ctorsA hmi
  have hml : mi < ctorsAs.length := (List.getElem?_eq_some_iff.mp hmi).1
  have := hall mi hml
  rw [hmi] at this
  cases hk : kinds[mi]? with
  | none => rw [hk] at this; exact nomatch this
  | some kss =>
    rw [hk] at this
    exact ⟨kss, rfl, this⟩

/-! ## The kinds' targets are members of the block — off the re-check

Lane NESTPOS (ARCH R2(b)): the bound is a conjunct of `blockOpenedOk`,
so it is read here from the check the model already inverts, and the
classifier (`ConLeche/Kernel/Inductives/Positivity.lean`) is consumed
by no proof. -/

/-- A recursive or reflexive kind the re-check accepted names a member. -/
theorem blockOpenedOk_tgt_lt {env₀ : Env} {names lps : List Name} {nP : Nat}
    {nIdxs : List Nat} {cty : Expr} {nF : Nat} {ks : List BlockFieldKind}
    (h : blockOpenedOk env₀ names lps nP nIdxs cty nF ks = true) {i t : Nat} (hi : i < nF)
    (hk : ks.getD i .ordinary = .recursive t ∨ ks.getD i .ordinary = .reflexive t) :
    t < names.length := by
  unfold blockOpenedOk at h
  split at h
  · split at h
    · simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
      have hall := h.2 i hi
      rename_i xFvs _ _
      cases hx : xFvs[i]? with
      | none =>
        rw [hx] at hall
        rcases hk with hk | hk <;> (rw [hk] at hall; exact nomatch hall)
      | some x =>
        rw [hx] at hall
        rcases hk with hk | hk
        · rw [hk] at hall
          dsimp only at hall
          cases hd : decide (t < names.length) with
          | true => exact of_decide_eq_true hd
          | false => rw [hd] at hall; simp at hall
        · rw [hk] at hall
          dsimp only at hall
          split at hall
          · cases hd : decide (t < names.length) with
            | true => exact of_decide_eq_true hd
            | false => rw [hd] at hall; simp at hall
          · exact nomatch hall
    · exact nomatch h
  · exact nomatch h

/-- **Every target a member's re-checked kinds carry is a member
index** — the `blockTgtsOf` reading the model's datum takes, at every
constructor and field position (a position with no inductive
hypothesis reads `0`, a member of a non-empty block). -/
theorem blockMemberFieldsOk_tgtsOf_lt {env₀ : Env} {names lps : List Name} {nP : Nat}
    {nIdxs : List Nat} {ctorsA : List (ConstantVal × Nat)}
    {kinds : List (List BlockFieldKind)} (hne : names ≠ [])
    (h : blockMemberFieldsOk env₀ names lps nP nIdxs ctorsA kinds = true) (j i : Nat) :
    (blockTgtsOf (kinds.getD j [])).getD i 0 < names.length := by
  have hpos : 0 < names.length := by
    cases names with
    | nil => exact absurd rfl hne
    | cons a l => simp
  have hlen : ctorsA.length = kinds.length := by
    simp only [blockMemberFieldsOk, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  by_cases hj : j < kinds.length
  · have hjA : j < ctorsA.length := by omega
    obtain ⟨ks, hks, hksLen, hop⟩ :=
      blockMemberFieldsOk_inv h (List.getElem?_eq_getElem hjA)
    have hgd : kinds.getD j [] = ks := by
      rw [List.getD_eq_getElem?_getD, hks]; rfl
    rw [hgd]
    simp only [blockTgtsOf, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases hki : ks[i]? with
    | none => simpa using hpos
    | some kk =>
      have hi : i < ks.length := (List.getElem?_eq_some_iff.mp hki).1
      have hgi : ks.getD i .ordinary = kk := by
        rw [List.getD_eq_getElem?_getD, hki]; rfl
      cases kk with
      | ordinary => simpa using hpos
      | negative => simpa using hpos
      | unsupported => simpa using hpos
      | recursive t =>
        exact blockOpenedOk_tgt_lt hop (by omega) (Or.inl hgi)
      | reflexive t =>
        exact blockOpenedOk_tgt_lt hop (by omega) (Or.inr hgi)
  · have hnil : kinds.getD j [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [hnil]
    simpa [blockTgtsOf] using hpos

/-! ## The install after the pass -/

/-- **The tail, inverted**: the elimination restriction (official's
`elim_only_at_universe_zero`), every member's index binders' sorts, the
kinds re-checked on the stored constructors, the constructors consed,
the RECURSOR STAGE — left opaque, as `checkBlockRec … = .ok rs`, so
that milestone M5's replacement fits without restating the tail — the
recursors consed with their rules, and the projection tables. -/
theorem checkBlockTail_inv {env env₂ : Env} {block : List ConstantInfo} {q : BlockPass Env}
    {F : Nat}
    (h : checkBlockTail (m := CheckM) (fueledOps mode F) env block q = .ok env₂) :
    ∃ (isorts : List (List Level))
      (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))),
      (q.p.large = true → q.p.resSort.isNeverZero = true ∨ (q.p.k < 2 ∧ q.p.numCtors < 2)) ∧
      checkBlockIdxSorts (fueledOps mode F) q.env₁ q.p.toBlockShape
        (q.p.members.zip q.cvTas) = .ok isorts ∧
      blockFieldsOk env q.p.memberNames q.p.lps q.p.nP q.p.nIdxs q.ctorsAs q.p.kinds = true ∧
      checkBlockPositivity (m := CheckM) (fueledOps mode F) q.env₁ q.env₁.find? q.env₁.consts
        q.p q.cvTas q.ctorsAs = .ok () ∧
      checkBlockRec (fueledOps mode F) (consBlockCtors q.p.nP q.ctorsAs q.env₁)
        q.p block q.cvTas q.ctorsAs = .ok rs ∧
      checkBlockTables (m := CheckM) q.p.toBlockShape
        (q.p.members.zip (q.ctorsAs.zip q.sortsss))
        (consBlockRecs (consBlockCtors q.p.nP q.ctorsAs q.env₁).find? q.p.toBlockShape q.p.nP 0 rs
          (consBlockCtors q.p.nP q.ctorsAs q.env₁)) = .ok env₂ := by
  rw [checkBlockTail] at h
  simp only [bind, Except.bind] at h
  by_cases hg : (q.p.large && !q.p.resSort.isNeverZero &&
      decide (2 ≤ q.p.k ∨ 2 ≤ q.p.numCtors)) = true
  · rw [if_pos hg] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_neg hg] at h
  have helim : q.p.large = true →
      q.p.resSort.isNeverZero = true ∨ (q.p.k < 2 ∧ q.p.numCtors < 2) := by
    intro hl
    cases hz : q.p.resSort.isNeverZero with
    | true => exact Or.inl rfl
    | false =>
      right
      refine Classical.byContradiction fun hge => hg ?_
      simp only [hl, hz, Bool.not_false, Bool.and_self, Bool.true_and, decide_eq_true_eq]
      omega
  try simp only [bind, Except.bind] at h
  cases hsorts : checkBlockIdxSorts (m := CheckM) (fueledOps mode F) q.env₁ q.p.toBlockShape
      (q.p.members.zip q.cvTas) with
  | error e => rw [hsorts] at h; exact nomatch h
  | ok isorts =>
  rw [hsorts] at h
  dsimp only at h
  by_cases hk : blockFieldsOk env q.p.memberNames q.p.lps q.p.nP q.p.nIdxs q.ctorsAs q.p.kinds
      = true
  case neg =>
    rw [if_neg hk] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hk] at h
  try simp only [bind, Except.bind] at h
  cases hPos : checkBlockPositivity (m := CheckM) (fueledOps mode F) q.env₁ q.env₁.find?
      q.env₁.consts q.p q.cvTas q.ctorsAs with
  | error e => rw [hPos] at h; exact nomatch h
  | ok u =>
  rw [hPos] at h
  dsimp only at h
  cases hRec : checkBlockRec (m := CheckM) (fueledOps mode F)
      (consBlockCtors q.p.nP q.ctorsAs q.env₁) q.p block q.cvTas q.ctorsAs with
  | error e => rw [hRec] at h; exact nomatch h
  | ok rs =>
  rw [hRec] at h
  dsimp only at h
  exact ⟨isorts, rs, helim, rfl, hk, rfl, rfl, h⟩

end ConLeche
