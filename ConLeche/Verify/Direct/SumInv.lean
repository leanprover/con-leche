import ConLeche.Verify.Direct.DirectInv
import ConLeche.Kernel.Direct.SumInstall

/-!
# The direct sum install's stage runs, inverted (task #175 sum-types,
indexed)

Each stage of `checkDirectSum` inverted to the facts the semantic
modules consume: the type former's run, every constructor's run at the
former's environment (`checkDirectSumCtors_inv`, positionally), the
generated recursor's comparison and every generated rule's run
(`checkDirectSumRules_inv`), and the recogniser's pins
(`directSumParts?_inv`).  Shape walks only, as `DirectInv.lean`.

Task #175 indexed: every stage carries the index count `nIdx`, the
constructor's residual is the family at the parameters followed by
`nIdx` index expressions (`directCtorResidOk`, inverted by
`residual_shape` below), and the field-sort walk is
`checkDirectFieldSortsI` (inverted by `checkDirectFieldSortsI_inv`,
whose large-eliminator clause admits a non-propositional field that is
one of the index expressions).
-/

namespace ConLeche

variable {mode : CheckMode}

private theorem sThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact sThrow_ne_ok (by assumption))
        | (exfalso; exact sThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-! ## The residual test, inverted (task #175 indexed) -/

/-- The head/arity/parameter-prefix test that `directCtorResidOk` and
the opened-residual guard perform, read back as a spine: the residual
is the head applied to the pinned parameter prefix followed by exactly
`nIdx` index expressions. -/
theorem residual_shape {e f : Expr} {ps : List Expr} {nP nIdx : Nat}
    (hfn : e.getAppFn = f) (htake : e.getAppArgs.take nP = ps)
    (hlen : e.getAppArgs.length = nP + nIdx) :
    ∃ es, e = Expr.mkAppN f (ps ++ es) ∧ es.length = nIdx := by
  refine ⟨e.getAppArgs.drop nP, ?_, ?_⟩
  · rw [← htake, List.take_append_drop, ← hfn, Expr.mkAppN_getApp]
  · rw [List.length_drop, hlen]; omega

/-! ## Stage 1: the type former -/

/-- `checkDirectSumTele`, inverted (task #195): either the declared
type was the telescope (the checked constant is the input, its type
strips to the sort), or the whnf'd telescope was checked from scratch
as the former's type at the block's name and level parameters — the
run of `checkConstantVal` is all the later stages consume, whichever
branch produced it. -/
theorem checkDirectSumTele_shape {env : Env} {cv : ConstantVal} {n : Nat}
    {cvTa₀ cvTa : ConstantVal} {s : Level} {F : Nat}
    (h : checkDirectSumTele (fueledOps mode F) env cv n cvTa₀ = .ok (cvTa, s)) :
    (cvTa = cvTa₀ ∧ ∃ bs, cvTa₀.type.stripPis n = some (bs, .sort s)) ∨
    ∃ ty, checkConstantVal (fueledOps mode F) env { cv with type := ty } = .ok cvTa := by
  unfold checkDirectSumTele at h
  split at h
  · next bs s' hst =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, bs, hst⟩
  · obtain ⟨q, -, h⟩ := exceptBind_ok h
    obtain ⟨bs, s'⟩ := q
    try simp only at h
    obtain ⟨cvTa', hccv, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨_, hccv⟩

theorem checkDirectSumInd_shape {env envI : Env} {p p' : DirectSumParts}
    {cvTa : ConstantVal} {F : Nat} {capsOf : DirectSumParts → IndCaps}
    (h : checkDirectSumInd (fueledOps mode F) env p capsOf = .ok (envI, cvTa, p')) :
    ∃ (cvT : ConstantVal) (s : Level),
      cvT.name = p.cvT.name ∧ cvT.levelParams = p.cvT.levelParams ∧
      checkConstantVal (fueledOps mode F) env cvT = .ok cvTa ∧
      p' = p.withSort s ∧
      envI = ⟨.indInfo cvTa (capsOf p') :: env.consts⟩ ∧
      ∃ bs, cvTa.type.stripPis (p.nP + p.nIdx) = some (bs, .sort s) := by
  unfold checkDirectSumInd at h
  obtain ⟨cvTa₀, hccv₀, h⟩ := exceptBind_ok h
  obtain ⟨q, htele, h⟩ := exceptBind_ok h
  obtain ⟨cvTa', s⟩ := q
  try simp only at h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨bs, tbody⟩ := q
  have hq' := unwrapOr_ok hq
  try simp only at h
  by_cases hc : (tbody == Expr.sort s) = true
  · rw [if_pos hc] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hstrip : cvTa'.type.stripPis (p.nP + p.nIdx) = some (bs, .sort s) := by
      rw [hq', beq_iff_eq.mp hc]
    rcases checkDirectSumTele_shape htele with ⟨rfl, -⟩ | ⟨ty, hccv⟩
    · exact ⟨p.cvT, s, rfl, rfl, hccv₀, rfl, rfl, bs, hstrip⟩
    · exact ⟨{ p.cvT with type := ty }, s, rfl, rfl, hccv, rfl, rfl, bs, hstrip⟩
  · rw [if_neg hc] at h
    close_throw

/-! ## Stage 2: one constructor -/

/-- `checkDirectFieldSortsI`, inverted (task #175 indexed): the sorts
are returned in field order, one per field, each the `ensureSort` of
the field annotation's inferred type at the field's own frame, under
the official universe bound (`isProp = false`) or — at a large
eliminator on a `Prop` family — the subsingleton-elimination criterion:
the field is a proposition OR one of the residual's index expressions
(`checkDirectFieldSorts_inv` widened). -/
theorem checkDirectFieldSortsI_inv {env : Env} {isProp large : Bool}
    {s : Level} {nP F : Nat} {fvs idxArgs : List Expr} :
    ∀ {j : Nat} {sorts : List Level},
      checkDirectFieldSortsI (fueledOps mode F) env isProp large s nP fvs idxArgs j
        = .ok sorts →
      sorts.length = j ∧
      ∀ i, i < j → ∃ fv ty u, fvs[i]? = some fv ∧ sorts[i]? = some u ∧
        inferTypeCore mode env F (nP + i) (Expr.fvarTypeD fv) = .ok ty ∧
        ensureSortCore mode env F (nP + i) ty = .ok u ∧
        (isProp = false → Level.leq u s = some true) ∧
        (isProp = true → large = true →
          (Level.isEquiv u .zero == some true) = true ∨ idxArgs.contains fv = true)
  | 0, sorts, h => by
    simp only [checkDirectFieldSortsI, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | j + 1, sorts, h => by
    unfold checkDirectFieldSortsI at h
    obtain ⟨fv, hfv, h⟩ := exceptBind_ok h
    have hfv' := unwrapOr_ok hfv
    try simp only at h
    obtain ⟨ty, hty₀, h⟩ := exceptBind_ok h
    have hty : inferTypeCore mode env F (nP + j) (Expr.fvarTypeD fv) = .ok ty := hty₀
    obtain ⟨u, hu₀, h⟩ := exceptBind_ok h
    have hu : ensureSortCore mode env F (nP + j) ty = .ok u := hu₀
    try simp only at h
    -- the guard, as one fact per branch
    suffices hs : ∃ rest,
        checkDirectFieldSortsI (fueledOps mode F) env isProp large s nP fvs idxArgs j
          = .ok rest ∧ sorts = rest ++ [u] ∧
        (isProp = false → Level.leq u s = some true) ∧
        (isProp = true → large = true →
          (Level.isEquiv u .zero == some true) = true ∨ idxArgs.contains fv = true) by
      obtain ⟨rest, hrest, rfl, hleq, hz⟩ := hs
      obtain ⟨hlen, hall⟩ := checkDirectFieldSortsI_inv hrest
      refine ⟨by simp [hlen], ?_⟩
      intro i hi
      rcases Nat.lt_or_ge i j with hij | hij
      · obtain ⟨fv', ty', u', hfv'', hu'', hty'', hen'', hl'', hz''⟩ :=
          hall i hij
        exact ⟨fv', ty', u', hfv'', by
          rw [List.getElem?_append_left (by omega)]; exact hu'', hty'', hen'',
          hl'', hz''⟩
      · obtain rfl : i = j := by omega
        exact ⟨fv, ty, u, hfv', by
          rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]; rfl,
          hty, hu, hleq, hz⟩
    by_cases hnp : (!isProp) = true
    · rw [if_pos hnp] at h
      obtain ⟨b, hb, h⟩ := exceptBind_ok h
      have hb' : Level.leq u s = some b := by
        cases hl : Level.leq u s with
        | none =>
          rw [hl] at hb
          exact absurd hb (by simp [liftFueled, throw, throwThe, MonadExceptOf.throw])
        | some b' =>
          rw [hl] at hb
          simp only [liftFueled, pure, Except.pure, Except.ok.injEq] at hb
          rw [hb]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        close_throw
      | true =>
      rw [if_pos rfl] at h
      simp only [pure, Except.pure, bind, Except.bind] at h
      obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
      simp only [Except.ok.injEq] at h
      refine ⟨rest, hrest, h.symm, fun _ => hb', fun hp => ?_⟩
      simp [hp] at hnp
    · rw [if_neg hnp] at h
      have hp : isProp = true := by simpa using hnp
      by_cases hl : large = true
      · rw [if_pos hl] at h
        by_cases hz : (Level.isEquiv u .zero == some true || idxArgs.contains fv) = true
        · rw [if_pos hz] at h
          simp only [pure, Except.pure, bind, Except.bind] at h
          obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
          simp only [Except.ok.injEq] at h
          refine ⟨rest, hrest, h.symm, fun h0 => ?_, fun _ _ => ?_⟩
          · rw [hp] at h0
            exact nomatch h0
          · exact Bool.or_eq_true_iff.mp hz
        · rw [if_neg hz] at h
          close_throw
      · rw [if_neg hl] at h
        simp only [pure, Except.pure, bind, Except.bind] at h
        obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
        simp only [Except.ok.injEq] at h
        refine ⟨rest, hrest, h.symm, fun h0 => ?_, fun _ h1 => absurd h1 hl⟩
        rw [hp] at h0
        exact nomatch h0

theorem checkDirectSumCtor_shape {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvC cvTa cvCa : ConstantVal}
    {nF : Nat} {F : Nat} {sorts : List Level}
    (h : checkDirectSumCtor (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok (cvCa, sorts)) :
    checkConstantVal (fueledOps mode F) env cvC = .ok cvCa ∧
    (∃ cbs es, cvCa.type.stripPis (nP + nF)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (directPsAt nF nP ++ es)) ∧
      es.length = nIdx) ∧
    ∃ (fvsP : List Expr) (crest : Expr) (tfvs : List Expr) (trest : Expr)
      (xFvs : List Expr) (idxArgs : List Expr),
      openPisAtFvars nP cvCa.type 0 = some (fvsP, crest) ∧
      openPisAtFvars nP cvTa.type 0 = some (tfvs, trest) ∧
      checkDirectDomsAt (fueledOps mode F) env 0 fvsP
        (tfvs.map Expr.fvarTypeD) nP = .ok () ∧
      openPisAtFvars nF crest nP
        = some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)) ∧
      idxArgs.length = nIdx ∧
      (∀ x ∈ xFvs, x.fvarTypeD.constsResolve env₀ = true) ∧
      (∀ e ∈ idxArgs, e.constsResolve env₀ = true) ∧
      checkDirectFieldSortsI (fueledOps mode F) env isProp large resSort
        nP xFvs idxArgs nF = .ok sorts := by
  unfold checkDirectSumCtor at h
  obtain ⟨cvCa', hccv, h⟩ := exceptBind_ok h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cbs, cbody⟩ := q
  have hq' := unwrapOr_ok hq
  try simp only at h
  by_cases hc : directCtorResidOk T lps nP nF nIdx cbody = true
  case neg => rw [if_neg hc] at h; close_throw
  rw [if_pos hc] at h
  obtain ⟨cq, hcq, h⟩ := exceptBind_ok h
  have hcq' := unwrapOr_ok hcq
  obtain ⟨fvsP, crest⟩ := cq
  obtain ⟨tq, htq, h⟩ := exceptBind_ok h
  have htq' := unwrapOr_ok htq
  obtain ⟨tfvs, trest⟩ := tq
  try simp only at h
  obtain ⟨u, hdoms, h⟩ := exceptBind_ok h
  obtain ⟨xq, hxq, h⟩ := exceptBind_ok h
  have hxq' := unwrapOr_ok hxq
  obtain ⟨xFvs, xrest⟩ := xq
  try simp only at h
  by_cases h2 : (xrest.getAppFn == Expr.const T (lps.map .param) &&
      xrest.getAppArgs.take nP == fvsP && xrest.getAppArgs.length == nP + nIdx) = true
  case neg => rw [if_neg h2] at h; close_throw
  rw [if_pos h2] at h
  by_cases h3 : (xFvs.all fun x => Expr.constsResolve env₀ x.fvarTypeD) = true
  case neg => rw [if_neg h3] at h; close_throw
  rw [if_pos h3] at h
  by_cases h4 : ((xrest.getAppArgs.drop nP).all fun e => Expr.constsResolve env₀ e) = true
  case neg => rw [if_neg h4] at h; close_throw
  rw [if_pos h4] at h
  obtain ⟨sorts', hsorts, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  -- the two residual tests, read back as spines
  simp only [directCtorResidOk, Bool.and_eq_true, beq_iff_eq] at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨es, hes, hesl⟩ := residual_shape hc.1.1 hc.2 hc.1.2
  refine ⟨hccv, ⟨cbs, es, by rw [hq', hes], hesl⟩,
    fvsP, crest, tfvs, trest, xFvs, xrest.getAppArgs.drop nP,
    hcq', htq', by cases u; exact hdoms, ?_, ?_, ?_, ?_, hsorts⟩
  · rw [hxq']
    congr 1
    rw [← h2.1.2, List.take_append_drop, ← h2.1.1, Expr.mkAppN_getApp]
  · rw [List.length_drop, h2.2]; omega
  · intro x hx
    exact List.all_eq_true.mp h3 x hx
  · intro e he
    exact List.all_eq_true.mp h4 e he

/-- All constructors, positionally: the annotated list is as long as
the input and every entry is its constructor's run. -/
theorem checkDirectSumCtors_inv {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal} {F : Nat} :
    ∀ {cs ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)},
      checkDirectSumCtors (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
        cvTa cs = .ok (ctorsA, sortss) →
      ctorsA.length = cs.length ∧ sortss.length = cs.length ∧
      ∀ (j : Nat) (c cA : ConstantVal × Nat), cs[j]? = some c → ctorsA[j]? = some cA →
        cA.2 = c.2 ∧
        ∃ sorts, sortss[j]? = some sorts ∧
        checkDirectSumCtor (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
          c.1 c.2 cvTa = .ok (cA.1, sorts)
  | [], ctorsA, sortss, h => by
    simp only [checkDirectSumCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, fun j c cA hc _ => by simp at hc⟩
  | c :: cs, ctorsA, sortss, h => by
    unfold checkDirectSumCtors at h
    obtain ⟨q, hc, h⟩ := exceptBind_ok h
    obtain ⟨cvCa, sorts⟩ := q
    try simp only at h
    obtain ⟨q', hrest, h⟩ := exceptBind_ok h
    obtain ⟨rest, srest⟩ := q'
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hlen, hlenS, hall⟩ := checkDirectSumCtors_inv hrest
    refine ⟨by simp [hlen], by simp [hlenS], ?_⟩
    intro j c' cA hc' hcA
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc' hcA
      subst hc'; subst hcA
      exact ⟨rfl, sorts, rfl, hc⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hc' hcA
      exact hall j c' cA hc' hcA

/-! ## Stage 3: the recursor -/

/-- The generated rules, positionally: rule `i` of the run from `j` is
the generator's rule `j + i`, scoped, and inferred. -/
theorem checkDirectSumRules_inv {env : Env} {rlps : List Name} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nIdx : Nat} {tty : Expr}
    {ctors : List (Name × Nat × Expr)} {F : Nat} :
    ∀ {k j : Nat} {rhss : List Expr},
      checkDirectSumRules (fueledOps mode F) env rlps T lps elim large nP nIdx tty ctors k j
        = .ok rhss →
      rhss.length = k ∧
      ∀ i, i < k → ∃ rhs, rhss[i]? = some rhs ∧
        directRecRhsI T lps elim large nP nIdx tty ctors (j + i) = some rhs ∧
        rhs.allLevelParamsDefined rlps = true ∧ rhs.constsResolve env = true ∧
        rhs.looseBVarsBounded 0 = true ∧ rhs.hasFvar = false ∧
        ∃ rhsTy, inferTypeCore mode env F 0 rhs = .ok rhsTy
  | 0, _, rhss, h => by
    simp only [checkDirectSumRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | k + 1, j, rhss, h => by
    unfold checkDirectSumRules at h
    obtain ⟨rhs, hrh, h⟩ := exceptBind_ok h
    have hrh' := unwrapOr_ok hrh
    try simp only at h
    by_cases h1 : (Expr.allLevelParamsDefined rlps rhs && Expr.constsResolve env rhs &&
        Expr.looseBVarsBounded 0 rhs && !rhs.hasFvar) = true
    case neg => rw [if_neg h1] at h; close_throw
    rw [if_pos h1] at h
    try simp only at h
    obtain ⟨rhsTy, hrty, h⟩ := exceptBind_ok h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := checkDirectSumRules_inv hrest
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
    refine ⟨by simp [hlen], ?_⟩
    intro i hi
    cases i with
    | zero =>
      exact ⟨rhs, rfl, by rw [Nat.add_zero]; exact hrh', h1.1.1.1, h1.1.1.2, h1.1.2, h1.2,
        rhsTy, hrty⟩
    | succ i =>
      obtain ⟨rhs', hget, hgen, hlp, hres, hbv, hfv, hty⟩ := hall i (by omega)
      have hget' : (rhs :: rest)[i + 1]? = some rhs' := by simpa using hget
      have hgen' : directRecRhsI T lps elim large nP nIdx tty ctors (j + (i + 1))
          = some rhs' := by
        rw [show j + (i + 1) = j + 1 + i from by omega]; exact hgen
      exact ⟨rhs', hget', hgen', hlp, hres, hbv, hfv, hty⟩

theorem checkDirectSumRec_shape {env : Env} {p : DirectSumParts}
    {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {F : Nat}
    (h : checkDirectSumRec (fueledOps mode F) env p cvTa ctorsA = .ok (cvRa, rhss)) :
    ∃ (cvRi : ConstantVal) (recTy sty : Expr) (u : Level),
      checkConstantVal (fueledOps mode F) env p.cvR = .ok cvRi ∧
      directRecTyI p.cvT.name p.cvT.levelParams p.elim p.large p.nP p.nIdx cvTa.type
        (ctorsA.map fun c => (c.1.name, c.2, c.1.type)) = some recTy ∧
      recTy.allLevelParamsDefined p.cvR.levelParams = true ∧
      recTy.constsResolve env = true ∧
      recTy.looseBVarsBounded 0 = true ∧ recTy.hasFvar = false ∧
      inferTypeCore mode env F 0 recTy = .ok sty ∧
      ensureSortCore mode env F 0 sty = .ok u ∧
      isDefEqCore mode env F 0 cvRi.type recTy = .ok true ∧
      checkDirectSumRules (fueledOps mode F) env p.cvR.levelParams p.cvT.name
        p.cvT.levelParams p.elim p.large p.nP p.nIdx cvTa.type
        (ctorsA.map fun c => (c.1.name, c.2, c.1.type))
        (ctorsA.map fun c => (c.1.name, c.2, c.1.type)).length 0 = .ok rhss ∧
      cvRa = ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ := by
  unfold checkDirectSumRec at h
  obtain ⟨cvRi, hcv, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨recTy, hrt, h⟩ := exceptBind_ok h
  have hrt' := unwrapOr_ok hrt
  try simp only at h
  by_cases h1 : (Expr.allLevelParamsDefined p.cvR.levelParams recTy &&
      Expr.constsResolve env recTy && Expr.looseBVarsBounded 0 recTy &&
      !recTy.hasFvar) = true
  case neg => rw [if_neg h1] at h; close_throw
  rw [if_pos h1] at h
  try simp only at h
  obtain ⟨sty, hsty, h⟩ := exceptBind_ok h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    close_throw
  | true =>
  rw [if_pos rfl] at h
  try simp only at h
  obtain ⟨rhss', hrules, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
  exact ⟨cvRi, recTy, sty, u, hcv, hrt', h1.1.1.1, h1.1.1.2, h1.1.2, h1.2, hsty, hu, hb,
    hrules, rfl⟩

/-! ## The recogniser -/

/-- The recogniser's pins (task #175 indexed): the one-constructor
exclusion is now conditional on the index count — a one-constructor
index-free block is the direct *structure* route — and every
constructor's residual is the family at the parameters followed by
exactly `nIdx` index expressions. -/
theorem directSumPartsCore?_inv {block : List ConstantInfo} {p : DirectSumParts}
    (h : directSumPartsCore? block = some p) :
    p.isProp = (Level.isEquiv p.resSort .zero == some true) ∧
    p.cvR.name = p.cvT.name.str "rec" ∧
    (p.ctors.length = 1 → p.nIdx ≠ 0) ∧
    (∀ c ∈ p.ctors, c.1.levelParams = p.cvT.levelParams ∧
      reservedBasisNames.contains c.1.name = false) ∧
    reservedBasisNames.contains p.cvT.name = false ∧
    reservedBasisNames.contains p.cvR.name = false ∧
    (p.large = true → p.elim ∈ p.cvR.levelParams) ∧
    (∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams) ∧
    p.rhss.length = p.ctors.length ∧
    (∀ c ∈ p.ctors, ∃ cbs es, c.1.type.stripPis (p.nP + c.2)
      = some (cbs, Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (directPsAt c.2 p.nP ++ es)) ∧ es.length = p.nIdx) := by
  unfold directSumPartsCore? at h
  split at h
  · next cvT caps rest =>
    split at h
    · next cs cvR mI rP rules hsplit =>
      try dsimp only at h
      split at h
      · exact nomatch h
      · next hbnd =>
        try dsimp only at h
        split at h
        · exact nomatch h
        · next hn1 =>
          try dsimp only at h
          split at h
          · next hc =>
            simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
            try dsimp only at h
            have hrules : rules.length = cs.length := by
              have := hc.2
              unfold directSumRulesOk at this
              simp only [Bool.and_eq_true, beq_iff_eq] at this
              exact this.1
            have hcs : ∀ c ∈ cs.map (fun c => (c.1, c.2.2)),
                c.1.levelParams = cvT.levelParams ∧
                reservedBasisNames.contains c.1.name = false := by
              intro c hc'
              obtain ⟨c', hc'', rfl⟩ := List.mem_map.mp hc'
              have := hc.1.2 c' hc''
              try simp only [Bool.and_eq_true, beq_iff_eq] at this
              exact ⟨this.1.1.2, this.1.2⟩
            have hres : ∀ c ∈ cs.map (fun c => (c.1, c.2.2)),
                ∃ cbs es, c.1.type.stripPis (rP - (cs.length + 1) + c.2)
                  = some (cbs, Expr.mkAppN (.const cvT.name (cvT.levelParams.map .param))
                    (directPsAt c.2 (rP - (cs.length + 1)) ++ es)) ∧
                  es.length = mI - rP := by
              intro c hc'
              obtain ⟨c', hc'', rfl⟩ := List.mem_map.mp hc'
              have hcc := hc.1.2 c' hc''
              try simp only [Bool.and_eq_true, beq_iff_eq] at hcc
              have hm := hcc.2
              split at hm
              · next cbs cbody hstrip =>
                simp only [directCtorResidOk, Bool.and_eq_true, beq_iff_eq] at hm
                obtain ⟨es, hes, hesl⟩ := residual_shape hm.1.1 hm.2 hm.1.2
                exact ⟨cbs, es, by rw [hstrip, hes], hesl⟩
              · exact absurd hm Bool.false_ne_true
            have hn1' : (cs.map (fun c => (c.1, c.2.2))).length = 1 → mI - rP ≠ 0 := by
              rw [List.length_map]
              intro h1 h0
              exact hn1 (by simp [h1, h0])
            split at h
            · next lq elim' hlarge =>
              obtain rfl := Option.some.inj h
              have hlps : ∀ q ∈ cvT.levelParams, q ∈ cvR.levelParams := by
                split at hlarge
                · next e relps hlp =>
                  split at hlarge
                  · next hcond =>
                    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                    intro q hq
                    rw [hlp]
                    exact List.mem_cons_of_mem _ (by rw [hcond.1]; exact hq)
                  · exact nomatch hlarge
                · exact nomatch hlarge
              refine ⟨rfl, hc.1.1.1.1, hn1', hcs, hc.1.1.1.2, hc.1.1.2, ?_, hlps, ?_, hres⟩
              · intro _
                show elim' ∈ cvR.levelParams
                split at hlarge
                · next e relps hlp =>
                  split at hlarge
                  · obtain rfl := Option.some.inj hlarge
                    rw [hlp]
                    exact List.mem_cons_self
                  · exact nomatch hlarge
                · exact nomatch hlarge
              · simp [hrules]
            · next lq hlarge =>
              split at h
              · next hcond =>
                obtain rfl := Option.some.inj h
                refine ⟨rfl, hc.1.1.1.1, hn1', hcs, hc.1.1.1.2, hc.1.1.2, ?_, ?_, ?_, hres⟩
                · intro hl
                  exact absurd hl Bool.false_ne_true
                · intro q hq
                  simp only [beq_iff_eq] at hcond
                  show q ∈ cvR.levelParams
                  rw [hcond]; exact hq
                · simp [hrules]
              · exact nomatch h
          · exact nomatch h
    · exact nomatch h
  · exact nomatch h

theorem directSumParts?_inv {env : Env} {block : List ConstantInfo} {p : DirectSumParts}
    (h : directSumParts? env block = some p) :
    p.isProp = (Level.isEquiv p.resSort .zero == some true) ∧
    p.cvR.name = p.cvT.name.str "rec" ∧
    (p.ctors.length = 1 → p.nIdx ≠ 0) ∧
    (∀ c ∈ p.ctors, c.1.levelParams = p.cvT.levelParams ∧
      reservedBasisNames.contains c.1.name = false) ∧
    reservedBasisNames.contains p.cvT.name = false ∧
    reservedBasisNames.contains p.cvR.name = false ∧
    (p.large = true → p.elim ∈ p.cvR.levelParams) ∧
    (∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams) ∧
    p.rhss.length = p.ctors.length ∧
    (∀ c ∈ p.ctors, ∃ cbs es, c.1.type.stripPis (p.nP + c.2)
      = some (cbs, Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (directPsAt c.2 p.nP ++ es)) ∧ es.length = p.nIdx) := by
  unfold directSumParts? at h
  cases hp : directSumPartsCore? block with
  | none => rw [hp] at h; exact nomatch h
  | some p' =>
    rw [hp] at h
    dsimp only at h
    by_cases hnr : directSumNonRec env p' = true
    · rw [if_pos hnr] at h
      obtain rfl := Option.some.inj h
      exact directSumPartsCore?_inv hp
    · rw [if_neg hnr] at h
      exact nomatch h

end ConLeche
