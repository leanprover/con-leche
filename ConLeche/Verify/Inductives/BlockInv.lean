module

public import ConLeche.Verify.Inductives.SumInv
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
* **the pass** (`checkBlockPass_inv`), whose last stage is the
  positivity function's run (inverted in `PositivityInv.lean`);
* **the tail** (`checkBlockIdxSorts_inv`, `checkBlockTail_inv`).

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
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    cases ho : Level.isEquiv s s0 with
    | none => rw [ho] at hb; exact nomatch hb
    | some b' =>
    rw [ho] at hb
    obtain rfl : b' = b := Except.ok.inj hb
    cases b' with
    | false => close_throw
    | true =>
    have hs : (Level.isEquiv s s0 == some true) = true := by simp [ho]
    try simp only [if_true] at h
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
theorem checkBlockCtors_inv {env₀ env : Env} {q : BlockShape} {F : Nat} :
    ∀ {l : List (MemberShape × ConstantVal)} {ctorsAs : List (List (ConstantVal × Nat))}
      {sortsss : List (List (List Level))},
      checkBlockCtors (fueledOps mode F) env₀ env q l = .ok (ctorsAs, sortsss) →
      ctorsAs.length = l.length ∧ sortsss.length = l.length ∧
      ∀ (i : Nat) (mc : MemberShape × ConstantVal), l[i]? = some mc →
        ∃ ctorsA sortss, ctorsAs[i]? = some ctorsA ∧ sortsss[i]? = some sortss ∧
          checkSumCtors (fueledOps mode F) env₀ env mc.1.cvT.name q.lps q.nP mc.1.nIdx
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

/-! ## The pass -/

/-- **One pass's shape at k members** (`checkNativePass_inv` at the
member list): the k formers' run at the record at the verdict `isRec`,
the constructors' runs per member at the environment holding ALL the
formers, the positivity function's run on the stored constructors, the
record completed, and the settling bit — the record at the walk's
`is_rec` against the one the pass ran at, at every member. -/
theorem checkBlockPass_inv {env : Env} {p₀ : BlockParts} {isRec : Bool}
    {q : BlockPass Env} {b : Bool} {F : Nat} {nst : Bool}
    (h : checkBlockPass (fueledOps mode F) env p₀ isRec nst = .ok (q, b)) :
    ∃ (p₁ : BlockShape),
      checkBlockInds (fueledOps mode F) env p₀ isRec = .ok (q.env₁, q.cvTas, p₁) ∧
      checkBlockCtors (fueledOps mode F) q.env₁ q.env₁ (p₀.complete p₁).toBlockShape
        ((p₀.complete p₁).members.zip q.cvTas) = .ok (q.ctorsAs, q.sortsss) ∧
      checkBlockPositivity (m := CheckM) (fueledOps mode F) q.env₁ q.env₁.find? q.env₁.consts
        (p₀.complete p₁) q.cvTas q.ctorsAs nst = .ok (q.kinds, q.nfs, q.nodes) ∧
      q.p = p₀.complete p₁ ∧
      b = ((List.range q.p.k).all fun i =>
        blockCapsAt q.p.toBlockShape i (nestIsRec q.kinds) == blockCapsAt p₁ i isRec) := by
  unfold checkBlockPass at h
  obtain ⟨r₁, hInd, h⟩ := exceptBind_ok h
  obtain ⟨env₁, cvTas, p₁⟩ := r₁
  try simp only at h
  obtain ⟨r₂, hCtors, h⟩ := exceptBind_ok h
  obtain ⟨ctorsAs, sortsss⟩ := r₂
  try simp only at h
  obtain ⟨⟨kinds, nfs, nodes⟩, hK, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨p₁, hInd, hCtors, hK, rfl, rfl⟩

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

/-! ## The install after the pass -/

/-- **The tail, inverted**: the elimination restriction (official's
`elim_only_at_universe_zero`), every member's index binders' sorts, the
constructors consed,
the RECURSOR STAGE — left opaque, as `checkBlockRec … = .ok out`, so
that milestone M5's replacement fits without restating the tail — the
recursors consed with their rules at their majors, and the projection
tables. -/
theorem checkBlockTail_inv {env₂ : Env} {block : List ConstantInfo} {q : BlockPass Env}
    {F : Nat} {nst : Bool}
    (h : checkBlockTail (m := CheckM) (fueledOps mode F) block q nst = .ok env₂) :
    ∃ (isorts : List (List Level))
      (out : List (ConstantVal × TargetMajor × List Expr)),
      (q.p.large = true → q.p.resSort.isNeverZero = true ∨ (q.p.k < 2 ∧ q.p.numCtors < 2)) ∧
      checkBlockIdxSorts (fueledOps mode F) q.env₁ q.p.toBlockShape
        (q.p.members.zip q.cvTas) = .ok isorts ∧
      checkBlockRec (fueledOps mode F) (consBlockCtors q.p.nP q.ctorsAs q.env₁)
        q.p nst (nst && blockNestedBit q.p.toBlockShape q.kinds) (nestKindsFlat q.kinds)
        q.nodes block q.cvTas q.ctorsAs (blockNormalCtors q.p.toBlockShape q.ctorsAs q.nfs)
          = .ok out ∧
      checkBlockTables (m := CheckM) q.p.toBlockShape
        (q.p.members.zip (q.ctorsAs.zip q.sortsss))
        (consBlockRecsT (consBlockCtors q.p.nP q.ctorsAs q.env₁).find?
          (·.constsResolve (consBlockCtors q.p.nP q.ctorsAs q.env₁)) q.p.toBlockShape 0 out
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
  cases hRec : checkBlockRec (m := CheckM) (fueledOps mode F)
      (consBlockCtors q.p.nP q.ctorsAs q.env₁) q.p nst
      (nst && blockNestedBit q.p.toBlockShape q.kinds) (nestKindsFlat q.kinds) q.nodes block q.cvTas
      q.ctorsAs (blockNormalCtors q.p.toBlockShape q.ctorsAs q.nfs) with
  | error e => rw [hRec] at h; exact nomatch h
  | ok out =>
  rw [hRec] at h
  dsimp only at h
  exact ⟨isorts, out, helim, rfl, rfl, h⟩

end ConLeche
