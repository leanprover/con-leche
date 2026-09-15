module

public import ConLeche.Verify.Inductives.SumInv
public import ConLeche.Kernel.Inductives.MutualInstall
import ConLeche.Verify.Inductives.FixParts

public section

/-!
# The mutual install: inversion (task #278)

The shape of a successful run of every monadic stage of the mutual
install (`ConLeche/Kernel/Inductives/MutualInstall.lean`), read off
the monad exactly as `FixInv.lean`/`SumInv.lean` read the fixpoint
route's: the block's shape guards, the formers' loop, the cross-member
checks, the constructors (with the member-aware normalisation), the
kinds' classification, the recursors' types and rules, and the
projection tables — closing with the whole chain of `∃`s
(`checkMutualCore_inv`, `checkMutual_inv`) that
`ConLeche/Semantics/Inductives/DeclMutual.lean` records as a run.

Shape walks only: `exceptBind_ok` per bind, `rw [if_pos …]` per guard
(the do-notation's join points defeat a bare `split`), `close_throw`
on the failing branches.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A thrown step never succeeds. -/
private theorem mutThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact mutThrow_ne_ok (by assumption))
        | (exfalso; exact mutThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-! ## A successful `mapM` in `Except`, positionally -/

/-- A successful `mapM` in the checker's monad yields as many results,
each its own element's run. -/
theorem mapM_except_inv {α β : Type} {f : α → CheckM β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r →
      r.length = l.length ∧
      ∀ i, i < l.length → ∃ a b, l[i]? = some a ∧ r[i]? = some b ∧ f a = .ok b
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | a :: l, r, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    obtain ⟨bs, hbs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := mapM_except_inv hbs
    refine ⟨by simp [hlen], ?_⟩
    intro i hi
    cases i with
    | zero => exact ⟨a, b, rfl, rfl, hb⟩
    | succ i =>
      obtain ⟨a', b', ha', hb', hf⟩ := hall i (by simpa using hi)
      exact ⟨a', b', by simpa using ha', by simpa using hb', hf⟩

/-! ## Stage 0: the block's shape -/

/-- Stage 0's guards, as the install checked them. -/
theorem mutualShapeOk_inv {b : MutualBlock} {u : Unit}
    (h : mutualShapeOk (m := CheckM) b = .ok u) :
    b.blockNames.Nodup ∧
    (b.formers.all (fun f => f.1.levelParams == b.lps) &&
      b.ctors.all (fun c => c.cv.levelParams == b.lps)) = true ∧
    b.ctors.all (fun c => c.member < b.k) = true ∧
    mutualCtorsGrouped b.ctors = true := by
  unfold mutualShapeOk at h
  by_cases h1 : b.blockNames.Nodup
  case neg => rw [if_neg h1] at h; close_throw
  rw [if_pos h1] at h
  try simp only [bind, Except.bind] at h
  by_cases h2 : (b.formers.all (fun f => f.1.levelParams == b.lps) &&
      b.ctors.all (fun c => c.cv.levelParams == b.lps)) = true
  case neg => rw [if_neg h2] at h; close_throw
  rw [if_pos h2] at h
  try simp only [bind, Except.bind] at h
  by_cases h3 : (b.ctors.all (fun c => c.member < b.k)) = true
  case neg => rw [if_neg h3] at h; close_throw
  rw [if_pos h3] at h
  try simp only [bind, Except.bind] at h
  by_cases h4 : mutualCtorsGrouped b.ctors = true
  case neg => rw [if_neg h4] at h; close_throw
  exact ⟨h1, h2, h3, h4⟩

/-! ## Stage 1: the formers -/

/-- The formers' loop at the empty block: nothing consed. -/
theorem mutualFormers_nil_inv {nP F : Nat} {env env' : Env} {fms : List MutualFormerA}
    (h : mutualFormers (fueledOps mode F) nP [] env = .ok (env', fms)) :
    env' = env ∧ fms = [] := by
  simp only [mutualFormers, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- **The formers' loop, one member at a time**: the constant check,
the telescope stage (task #195), the result sort read off the
telescope, and the rest of the loop at the environment holding this
former with the block's capability record (`{}`). -/
theorem mutualFormers_inv {nP F : Nat} {cv : ConstantVal} {nIdx : Nat}
    {rest : List (ConstantVal × Nat)} {env env' : Env} {fms : List MutualFormerA}
    (h : mutualFormers (fueledOps mode F) nP ((cv, nIdx) :: rest) env = .ok (env', fms)) :
    ∃ (cvTa₀ cvTa : ConstantVal) (s : Level) (bs : List (Expr × BinderMeta))
      (fs : List MutualFormerA),
      checkConstantVal (fueledOps mode F) env cv = .ok cvTa₀ ∧
      checkSumTele (fueledOps mode F) env cv (nP + nIdx) cvTa₀ = .ok (cvTa, s) ∧
      cvTa.type.stripPis (nP + nIdx) = some (bs, Expr.sort s) ∧
      mutualFormers (fueledOps mode F) nP rest ⟨.indInfo cvTa {} :: env.consts⟩
        = .ok (env', fs) ∧
      fms = ⟨cvTa, nIdx, s⟩ :: fs := by
  unfold mutualFormers at h
  obtain ⟨cvTa₀, hccv, h⟩ := exceptBind_ok h
  obtain ⟨q, htele, h⟩ := exceptBind_ok h
  obtain ⟨cvTa, s⟩ := q
  try simp only at h
  obtain ⟨q2, hq2, h⟩ := exceptBind_ok h
  obtain ⟨bs, tbody⟩ := q2
  have hq2' := unwrapOr_ok hq2
  try simp only at h
  by_cases hc : (tbody == Expr.sort s) = true
  case neg => rw [if_neg hc] at h; close_throw
  rw [if_pos hc] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨q3, hrec, h⟩ := exceptBind_ok h
  obtain ⟨env'', fs⟩ := q3
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨cvTa₀, cvTa, s, bs, fs, hccv, htele, by rw [hq2', beq_iff_eq.mp hc], hrec, rfl⟩

/-! ## Stage 2: the cross-member checks -/

/-- Official's parameter-domain comparison, inverted: every position
below the walk's bound carries a successful `isDefEq` at its own
frame. -/
theorem mutualDomsOk_inv {env : Env} {F : Nat} {fvs doms : List Expr} :
    ∀ {j : Nat}, mutualDomsOk (fueledOps mode F) env fvs doms j = .ok () →
      ∀ i, i < j → ∃ a b, fvs[i]? = some a ∧ doms[i]? = some b ∧
        isDefEqCore mode env F i (Expr.fvarTypeD a) b = .ok true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | j + 1, h, i, hi => by
    unfold mutualDomsOk at h
    obtain ⟨a, ha, h⟩ := exceptBind_ok h
    have ha' := unwrapOr_ok ha
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    have hb' := unwrapOr_ok hb
    try simp only at h
    obtain ⟨c, hc, h⟩ := exceptBind_ok h
    have hc' : isDefEqCore mode env F j (Expr.fvarTypeD a) b = .ok c := hc
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      close_throw
    | true =>
    rw [if_pos rfl] at h
    try simp only at h
    rcases Nat.lt_or_ge i j with hij | hij
    · exact mutualDomsOk_inv h i hij
    · obtain rfl : i = j := by omega
      exact ⟨a, b, ha', hb', hc'⟩

/-- **The cross-member checks, one member at a time**: the result sort
equivalent to the first former's, the former's parameter telescope
opened, and its parameter domains definitionally the first's. -/
theorem mutualCrossChecks_inv {env : Env} {nP F : Nat} {f₀ f : MutualFormerA}
    {doms₀ : List Expr} {rest : List MutualFormerA} {u : Unit}
    (h : mutualCrossChecks (fueledOps mode F) env nP f₀ doms₀ (f :: rest) = .ok u) :
    Level.isEquiv f.s f₀.s = some true ∧
    ∃ tq, openPisAtFvars nP f.cvTa.type 0 = some tq ∧
      mutualDomsOk (fueledOps mode F) env tq.1 doms₀ nP = .ok () ∧
      mutualCrossChecks (fueledOps mode F) env nP f₀ doms₀ rest = .ok () := by
  unfold mutualCrossChecks at h
  obtain ⟨c, hc, h⟩ := exceptBind_ok h
  have hc' : Level.isEquiv f.s f₀.s = some c := by
    cases hl : Level.isEquiv f.s f₀.s with
    | none =>
      rw [hl] at hc
      exact absurd hc (by simp [liftFueled, throw, throwThe, MonadExceptOf.throw])
    | some c' =>
      rw [hl] at hc
      simp only [liftFueled, pure, Except.pure, Except.ok.injEq] at hc
      rw [hc]
  cases c with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    close_throw
  | true =>
  rw [if_pos rfl] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨tq, htq, h⟩ := exceptBind_ok h
  have htq' := unwrapOr_ok htq
  try simp only at h
  obtain ⟨w, hdoms, h⟩ := exceptBind_ok h
  refine ⟨hc', tq, htq', by cases w; exact hdoms, ?_⟩
  cases hrest : mutualCrossChecks (m := CheckM) (fueledOps mode F) env nP f₀ doms₀ rest with
  | error e => rw [hrest] at h; exact nomatch h
  | ok w' => cases w'; rfl

/-! ## Stage 3: the constructors -/

/-- **Official's positivity walk as a normalisation**, inverted: the
domain mentions no member (and is returned as it is), or it was
`whnf`'d and either returned, or walked under one Π binder whose
domain mentions no member. -/
theorem normPosDomM_inv {env : Env} {memberNames : List Name} {F : Nat} :
    ∀ {d fuel : Nat} {e e' : Expr},
      normPosDomM (fueledOps mode F) env memberNames d fuel e = .ok e' →
      (mentionsMember memberNames e = false ∧ e' = e) ∨
      ∃ w, ConLeche.whnf mode env F d e = .ok w ∧
        (e' = w ∨
          ∃ (dom body : Expr) (bm : BinderMeta) (body' : Expr) (fuel' : Nat),
            fuel = fuel' + 1 ∧ w = .forallE dom body bm ∧
            mentionsMember memberNames dom = false ∧
            normPosDomM (fueledOps mode F) env memberNames (d + 1) fuel'
              (body.instantiate1 (.fvar d dom)) = .ok body' ∧
            e' = .forallE dom (body'.abstract1 d) bm) := by
  intro d fuel
  cases fuel with
  | zero => intro e e' h; simp only [normPosDomM] at h; close_throw
  | succ fuel =>
    intro e e' h
    unfold normPosDomM at h
    by_cases hm : mentionsMember memberNames e = true
    case neg =>
      rw [if_pos (by simpa using hm)] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl ⟨by simpa using hm, h.symm⟩
    rw [if_neg (by simpa using hm)] at h
    try simp only [bind, Except.bind] at h
    obtain ⟨w, hw, h⟩ := exceptBind_ok h
    have hw' : ConLeche.whnf mode env F d e = .ok w := hw
    by_cases hmw : mentionsMember memberNames w = true
    case neg =>
      rw [if_pos (by simpa using hmw)] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inr ⟨w, hw', Or.inl h.symm⟩
    rw [if_neg (by simpa using hmw)] at h
    refine Or.inr ⟨w, hw', ?_⟩
    cases w
    case forallE dom body bm =>
      simp only at h
      by_cases hd : mentionsMember memberNames dom = true
      · rw [if_pos hd] at h; close_throw
      rw [if_neg hd] at h
      try simp only [bind, Except.bind] at h
      obtain ⟨body', hbody, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inr ⟨dom, body, bm, body', fuel, rfl, rfl, by simpa using hd, hbody, h.symm⟩
    all_goals
      (simp only [pure, Except.pure, Except.ok.injEq] at h
       exact Or.inl h.symm)

/-- `normFieldDoms` at a mutual block, at the end of the telescope. -/
theorem normFieldDomsM_zero_inv {env : Env} {memberNames : List Name} {F i : Nat} {e : Expr}
    {bs : List (Expr × BinderMeta)} {r : Expr}
    (h : normFieldDomsM (fueledOps mode F) env memberNames i 0 e = .ok (bs, r)) :
    bs = [] ∧ r = e := by
  simp only [normFieldDomsM, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- `normFieldDoms` at a mutual block, one field at a time. -/
theorem normFieldDomsM_inv {env : Env} {memberNames : List Name} {F i n : Nat} {e : Expr}
    {bs : List (Expr × BinderMeta)} {r : Expr}
    (h : normFieldDomsM (fueledOps mode F) env memberNames i (n + 1) e = .ok (bs, r)) :
    ∃ (dom body : Expr) (bm : BinderMeta) (dom' : Expr) (bs' : List (Expr × BinderMeta)),
      e = .forallE dom body bm ∧
      normPosDomM (fueledOps mode F) env memberNames i 1024 dom = .ok dom' ∧
      normFieldDomsM (fueledOps mode F) env memberNames (i + 1) n
        (body.instantiate1 (.fvar i dom)) = .ok (bs', r) ∧
      bs = (dom', bm) :: bs' := by
  cases e
  case forallE dom body bm =>
    rw [normFieldDomsM] at h
    obtain ⟨dom', hdom, h⟩ := exceptBind_ok h
    obtain ⟨q, hq, h⟩ := exceptBind_ok h
    obtain ⟨bs', r'⟩ := q
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨dom, body, bm, dom', bs', rfl, hdom, hq, rfl⟩
  all_goals rw [normFieldDomsM] at h
  all_goals first
    | close_throw
    | (intro _ _ _ hx; exact Expr.noConfusion hx)

/-- The normalisation stage stores either the constructor as checked
or a from-scratch check of the rebuilt constant — in both cases some
constant with the declared name and level parameters (the fixpoint
route's `normCtorVal_inv` over the member list). -/
theorem normCtorValM_inv {env : Env} {memberNames : List Name} {nP nF F : Nat}
    {cvC cvCa₀ cvCa : ConstantVal}
    (h₀ : checkConstantVal (fueledOps mode F) env cvC = .ok cvCa₀)
    (h : normCtorValM (fueledOps mode F) env memberNames nP nF cvC cvCa₀ = .ok cvCa) :
    ∃ ty', checkConstantVal (fueledOps mode F) env { cvC with type := ty' } = .ok cvCa := by
  unfold normCtorValM at h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cbs, _⟩ := q
  try simp only at h
  obtain ⟨r, hr, h⟩ := exceptBind_ok h
  obtain ⟨fvsP, crest⟩ := r
  try simp only at h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  obtain ⟨fbs, resid⟩ := u
  try simp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨cvC.type, h₀⟩
  · exact ⟨_, h⟩

/-- **One constructor's stage**, inverted (`checkSumCtor_shape` with
the member-aware normalisation and the residual pinned at the
constructor's own member). -/
theorem checkMutualCtor_shape {env : Env} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal} {nF F : Nat} {sorts : List Level}
    (h : checkMutualCtor (fueledOps mode F) env memberNames T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok (cvCa, sorts)) :
    (∃ ty', checkConstantVal (fueledOps mode F) env { cvC with type := ty' } = .ok cvCa) ∧
    (∃ cbs es, cvCa.type.stripPis (nP + nF)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (structPsAt nF nP ++ es)) ∧
      es.length = nIdx) ∧
    ∃ (fvsP : List Expr) (crest : Expr) (tfvs : List Expr) (trest : Expr)
      (xFvs idxArgs : List Expr),
      openPisAtFvars nP cvCa.type 0 = some (fvsP, crest) ∧
      openPisAtFvars nP cvTa.type 0 = some (tfvs, trest) ∧
      checkStructDomsAt (fueledOps mode F) env 0 fvsP
        (tfvs.map Expr.fvarTypeD) nP = .ok () ∧
      openPisAtFvars nF crest nP
        = some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)) ∧
      idxArgs.length = nIdx ∧
      (∀ x ∈ xFvs, x.fvarTypeD.constsResolve env = true) ∧
      (∀ e ∈ idxArgs, e.constsResolve env = true) ∧
      checkStructFieldSortsI (fueledOps mode F) env isProp large resSort
        nP xFvs idxArgs nF = .ok sorts := by
  unfold checkMutualCtor at h
  obtain ⟨cvCa₀, hccv₀, h⟩ := exceptBind_ok h
  obtain ⟨cvCa', hnorm, h⟩ := exceptBind_ok h
  have hccv := normCtorValM_inv hccv₀ hnorm
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cbs, cbody⟩ := q
  have hq' := unwrapOr_ok hq
  try simp only at h
  by_cases hc : structCtorResidOk T lps nP nF nIdx cbody = true
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
  by_cases h3 : (xFvs.all fun x => Expr.constsResolve env x.fvarTypeD) = true
  case neg => rw [if_neg h3] at h; close_throw
  rw [if_pos h3] at h
  by_cases h4 : ((xrest.getAppArgs.drop nP).all fun e => Expr.constsResolve env e) = true
  case neg => rw [if_neg h4] at h; close_throw
  rw [if_pos h4] at h
  obtain ⟨sorts', hsorts, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [structCtorResidOk, Bool.and_eq_true, beq_iff_eq] at hc
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
the input and every entry is its constructor's run at its own
member's former. -/
theorem checkMutualCtors_inv {env : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {isProp : Bool} {F : Nat} :
    ∀ {cs : List MutualCtor} {ctorsA : List (ConstantVal × Nat)}
      {sortss : List (List Level)},
      checkMutualCtors (fueledOps mode F) env b fms isProp cs = .ok (ctorsA, sortss) →
      ctorsA.length = cs.length ∧ sortss.length = cs.length ∧
      ∀ (j : Nat) (c : MutualCtor) (cA : ConstantVal × Nat),
        cs[j]? = some c → ctorsA[j]? = some cA →
        cA.2 = c.nF ∧
        ∃ sorts, sortss[j]? = some sorts ∧
          checkMutualCtor (fueledOps mode F) env b.memberNames
            (fms.getD c.member default).cvTa.name b.lps b.nP (fms.getD c.member default).nIdx
            (fms.getD c.member default).s isProp b.large c.cv c.nF
            (fms.getD c.member default).cvTa = .ok (cA.1, sorts)
  | [], ctorsA, sortss, h => by
    simp only [checkMutualCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, fun j c cA hc _ => by simp at hc⟩
  | c :: cs, ctorsA, sortss, h => by
    unfold checkMutualCtors at h
    obtain ⟨q, hc, h⟩ := exceptBind_ok h
    obtain ⟨cvCa, sorts⟩ := q
    try simp only at h
    obtain ⟨q', hrest, h⟩ := exceptBind_ok h
    obtain ⟨rest, srest⟩ := q'
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hlen, hlenS, hall⟩ := checkMutualCtors_inv hrest
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

/-- The kinds' classification at install: the recogniser's syntactic
reading of the stored constructors, with no non-positive and no
unmodeled occurrence. -/
theorem classifyMutualKinds_inv {members : List (Name × Nat × Nat)} {lps : List Name}
    {nP : Nat} {ctorsA : List (ConstantVal × Nat)}
    {kinds : List (List (RecFieldKind × Nat))}
    (h : classifyMutualKinds (m := CheckM) members lps nP ctorsA = .ok kinds) :
    ctorsA.mapM (mutualCtorKinds members lps nP) = some kinds ∧
    kinds.any (fun ks => ks.any (·.1 == .negative)) = false ∧
    kinds.any (fun ks => ks.any (·.1 == .unsupported)) = false ∧
    kinds.length = ctorsA.length := by
  unfold classifyMutualKinds at h
  cases hk : ctorsA.mapM (mutualCtorKinds members lps nP) with
  | none => rw [hk] at h; exact nomatch h
  | some ks =>
  rw [hk] at h
  simp only [unwrapOr, bind, Except.bind, pure, Except.pure] at h
  by_cases hneg : ks.any (fun ks => ks.any (·.1 == .negative)) = true
  · rw [if_pos hneg] at h; exact nomatch h
  rw [if_neg hneg] at h
  by_cases hun : ks.any (fun ks => ks.any (·.1 == .unsupported)) = true
  · rw [if_pos hun] at h; exact nomatch h
  rw [if_neg hun] at h
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨rfl, by simpa using hneg, by simpa using hun, List.mapM_option_length hk⟩

/-! ## Stage 4: the recursors -/

/-- **One member's recursor type**: generated, scoped, inferred, and —
when the stream carries a record — compared with it by one `isDefEq`. -/
theorem checkMutualRecTy_shape {env : Env} {b : MutualBlock} {formers4 : List MutualFormer}
    {ctors4 : List MutualCtor4} {mIdx F : Nat} {streamRec : Option ConstantVal}
    {cvRa : ConstantVal}
    (h : checkMutualRecTy (fueledOps mode F) env b formers4 ctors4 mIdx streamRec
      = .ok cvRa) :
    ∃ (recTy sty : Expr) (u : Level),
      mutualRecTy b.lps b.elim b.large b.nP formers4 ctors4 mIdx = some recTy ∧
      recTy.allLevelParamsDefined b.rlps = true ∧
      recTy.constsResolve env = true ∧
      recTy.looseBVarsBounded 0 = true ∧ recTy.hasFvar = false ∧
      inferTypeCore mode env F 0 recTy = .ok sty ∧
      ensureSortCore mode env F 0 sty = .ok u ∧
      (∀ cvR, streamRec = some cvR → ∃ cvRi,
        checkConstantVal (fueledOps mode F) env cvR = .ok cvRi ∧
        isDefEqCore mode env F 0 cvRi.type recTy = .ok true) ∧
      cvRa = ⟨b.recName mIdx, b.rlps, recTy⟩ := by
  unfold checkMutualRecTy at h
  obtain ⟨recTy, hrt, h⟩ := exceptBind_ok h
  have hrt' := unwrapOr_ok hrt
  try simp only at h
  by_cases h1 : (Expr.allLevelParamsDefined b.rlps recTy && Expr.constsResolve env recTy &&
      Expr.looseBVarsBounded 0 recTy && !recTy.hasFvar) = true
  case neg => rw [if_neg h1] at h; close_throw
  rw [if_pos h1] at h
  try simp only at h
  obtain ⟨sty, hsty, h⟩ := exceptBind_ok h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
  cases hsr : streamRec with
  | none =>
    rw [hsr] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨recTy, sty, u, hrt', h1.1.1.1, h1.1.1.2, h1.1.2, h1.2, hsty, hu,
      (fun cvR hcv => nomatch hcv), h.symm⟩
  | some cvR =>
    rw [hsr] at h
    try simp only at h
    obtain ⟨cvRi, hcvi, h⟩ := exceptBind_ok h
    obtain ⟨bb, hb, h⟩ := exceptBind_ok h
    cases bb with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      close_throw
    | true =>
    rw [if_pos rfl] at h
    try simp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    refine ⟨recTy, sty, u, hrt', h1.1.1.1, h1.1.1.2, h1.1.2, h1.2, hsty, hu, ?_, h.symm⟩
    intro cvR' hcv
    obtain rfl := Option.some.inj hcv
    exact ⟨cvRi, hcvi, hb⟩

/-- The recursor types over the members, positionally. -/
theorem checkMutualRecTys_inv {env : Env} {b : MutualBlock} {formers4 : List MutualFormer}
    {ctors4 : List MutualCtor4} {F : Nat}
    {streamRecs : Option (List (ConstantVal × List RecRule))} :
    ∀ {k : Nat} {cvRas : List ConstantVal},
      checkMutualRecTys (fueledOps mode F) env b formers4 ctors4 streamRecs k = .ok cvRas →
      cvRas.length = k ∧
      ∀ i, i < k → ∃ cvRa, cvRas[i]? = some cvRa ∧
        checkMutualRecTy (fueledOps mode F) env b formers4 ctors4 i
          (streamRecs.bind fun rs => (rs[i]?).map (·.1)) = .ok cvRa
  | 0, cvRas, h => by
    simp only [checkMutualRecTys, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | k + 1, cvRas, h => by
    unfold checkMutualRecTys at h
    obtain ⟨earlier, hearlier, h⟩ := exceptBind_ok h
    try simp only at h
    obtain ⟨cvRa, hrec, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := checkMutualRecTys_inv hearlier
    refine ⟨by simp [hlen], ?_⟩
    intro i hi
    rcases Nat.lt_or_ge i k with hik | hik
    · obtain ⟨cvRa', hget, hrun⟩ := hall i hik
      exact ⟨cvRa', by rw [List.getElem?_append_left (by omega)]; exact hget, hrun⟩
    · obtain rfl : i = k := by omega
      exact ⟨cvRa, by rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]; rfl, hrec⟩

-- The per-rule facts of the mapM tail, shared by the two arms of the
-- stream-record split.
local syntax "rules_tail " term ", " term : tactic
local macro_rules
  | `(tactic| rules_tail $bb, $ee) =>
    `(tactic| (obtain ⟨hlen, hall⟩ := mapM_except_inv ‹_›
               refine ⟨hlen, ?_⟩
               intro i hi
               obtain ⟨a, bres, ha, hb, hf⟩ := hall i hi
               obtain ⟨J, c⟩ := a
               simp only at hf
               obtain ⟨rhs, hrhs, hf⟩ := exceptBind_ok hf
               have hrhs' := unwrapOr_ok hrhs
               try simp only at hf
               by_cases hg : (Expr.allLevelParamsDefined ($bb).rlps rhs &&
                   Expr.constsResolve $ee rhs && Expr.looseBVarsBounded 0 rhs &&
                   !rhs.hasFvar) = true
               case neg =>
                 rw [if_neg hg] at hf
                 exact absurd hf (by
                   simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map,
                     bind, Except.bind])
               rw [if_pos hg] at hf
               simp only [pure, Except.pure, Except.ok.injEq] at hf
               subst hf
               simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hg
               exact ⟨J, c, rhs, ha, hb, hrhs', hg.1.1.1, hg.1.1.2, hg.1.2, hg.2⟩))

/-- **One member's rules**: the stream's compared structurally when
given, then every own constructor's generated right-hand side, scoped
at the environment holding the rule-less recursors. -/
theorem checkMutualMemberRules_inv {envR : Env} {b : MutualBlock}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4} {mIdx : Nat}
    {streamRec : Option (ConstantVal × List RecRule)} {rules : List (MutualCtor × Expr)}
    (h : checkMutualMemberRules (m := CheckM) envR b formers4 ctors4 mIdx streamRec
      = .ok rules) :
    (∀ cvR rs, streamRec = some (cvR, rs) →
      mutualRulesOk b.recName (b.rlps.map Level.param) b.nP b.k b.n ctors4
        ((b.ownCtors mIdx).map (·.1)) (rs.map (·.rhs)) cvR.type = true) ∧
    rules.length = (b.ownCtors mIdx).length ∧
    ∀ i, i < (b.ownCtors mIdx).length →
      ∃ (J : Nat) (c : MutualCtor) (rhs : Expr),
        (b.ownCtors mIdx)[i]? = some (J, c) ∧ rules[i]? = some (c, rhs) ∧
        mutualRecRhs b.lps b.elim b.large b.nP formers4 ctors4 b.recName
          (b.rlps.map Level.param) J = some rhs ∧
        rhs.allLevelParamsDefined b.rlps = true ∧ rhs.constsResolve envR = true ∧
        rhs.looseBVarsBounded 0 = true ∧ rhs.hasFvar = false := by
  simp only [checkMutualMemberRules] at h
  split at h
  · next cvR rs =>
    by_cases hok : mutualRulesOk b.recName (b.rlps.map Level.param) b.nP b.k b.n ctors4
        ((b.ownCtors mIdx).map (·.1)) (rs.map (·.rhs)) cvR.type = true
    case neg => rw [if_neg hok] at h; close_throw
    rw [if_pos hok] at h
    refine ⟨?_, ?_⟩
    · intro cvR' rs' heq
      have heq' := Option.some.inj heq
      injection heq' with e1 e2
      subst e1; subst e2
      exact hok
    · rules_tail b, envR
  · next hno =>
    refine ⟨fun cvR' rs' heq => (hno cvR' rs' heq).elim, ?_⟩
    rules_tail b, envR

/-- The rules over the members, positionally. -/
theorem checkMutualAllRules_inv {envR : Env} {b : MutualBlock}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4}
    {streamRecs : Option (List (ConstantVal × List RecRule))} :
    ∀ {k : Nat} {rulesOf : List (List (MutualCtor × Expr))},
      checkMutualAllRules (m := CheckM) envR b formers4 ctors4 streamRecs k = .ok rulesOf →
      rulesOf.length = k ∧
      ∀ i, i < k → ∃ rules, rulesOf[i]? = some rules ∧
        checkMutualMemberRules (m := CheckM) envR b formers4 ctors4 i
          (streamRecs.bind (·[i]?)) = .ok rules
  | 0, rulesOf, h => by
    simp only [checkMutualAllRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | k + 1, rulesOf, h => by
    unfold checkMutualAllRules at h
    obtain ⟨earlier, hearlier, h⟩ := exceptBind_ok h
    try simp only at h
    obtain ⟨rules, hrules, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := checkMutualAllRules_inv hearlier
    refine ⟨by simp [hlen], ?_⟩
    intro i hi
    rcases Nat.lt_or_ge i k with hik | hik
    · obtain ⟨rules', hget, hrun⟩ := hall i hik
      exact ⟨rules', by rw [List.getElem?_append_left (by omega)]; exact hget, hrun⟩
    · obtain rfl : i = k := by omega
      exact ⟨rules, by rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]; rfl,
        hrules⟩

/-! ## Stage 5: the projection tables -/

/-- One member's table stage: nothing, or the table of a
structure-like member (one constructor, no index). -/
theorem mutualMemberTable_inv {b : MutualBlock} {f : MutualFormerA}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} {mIdx : Nat}
    {env env' : Env}
    (h : mutualMemberTable (m := CheckM) b f ctorsA sortss mIdx env = .ok env') :
    env' = env ∨
    ∃ (J : Nat) (c : MutualCtor),
      b.ownCtors mIdx = [(J, c)] ∧ f.nIdx = 0 ∧
      checkStructProjTable (m := CheckM) f.cvTa.name c.cv.name b.lps b.nP c.nF f.s
        (structProjGuards (ctorsA.getD J default).1.type b.nP c.nF (sortss.getD J []))
        1 (ctorsA.getD J default).1 env = .ok env' := by
  unfold mutualMemberTable at h
  split at h
  · next J c heq =>
    by_cases hn : (f.nIdx == 0) = true
    · rw [if_pos hn] at h
      exact Or.inr ⟨J, c, heq, by simpa using hn, h⟩
    · rw [if_neg hn] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm

/-- The table stage over the members, one at a time. -/
theorem mutualTables_nil_inv {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} {env env' : Env}
    (h : mutualTables (m := CheckM) b ctorsA sortss [] env = .ok env') : env' = env := by
  simp only [mutualTables, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

/-- The table stage over the members, one at a time. -/
theorem mutualTables_inv {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} {f : MutualFormerA} {mIdx : Nat}
    {rest : List (MutualFormerA × Nat)} {env env' : Env}
    (h : mutualTables (m := CheckM) b ctorsA sortss ((f, mIdx) :: rest) env = .ok env') :
    ∃ envI, mutualMemberTable (m := CheckM) b f ctorsA sortss mIdx env = .ok envI ∧
      mutualTables (m := CheckM) b ctorsA sortss rest envI = .ok env' := by
  unfold mutualTables at h
  obtain ⟨envI, hI, h⟩ := exceptBind_ok h
  exact ⟨envI, hI, h⟩

/-! ## The recogniser's pin -/

/-- **The recursor records' structural pin, at one member**: the
record is NAMED the recursor official generates (`T_m.rec`).  The
install throws on the pin (`checkMutual`), so a successful run reads
it off here. -/
theorem mutualRecPinOk_name {p : MutualParts} (h : mutualRecPinOk p = true)
    {m : Nat} (hm : m < p.k) {mb : MutualMember} (hmb : p.members[m]? = some mb) :
    mb.cvR.name = mb.cv.name.str "rec" := by
  simp only [mutualRecPinOk, List.all_eq_true, List.mem_range] at h
  have hm' := h m hm
  rw [hmb] at hm'
  simp only [Bool.and_eq_true, beq_iff_eq] at hm'
  exact hm'.1.1.1.1

/-- The block record's recursor name at a member, read off the
recogniser's member list. -/
theorem MutualParts.toBlock_recName {p : MutualParts} {m : Nat} {mb : MutualMember}
    (hmb : p.members[m]? = some mb) :
    p.toBlock.recName m = mb.cv.name.str "rec" := by
  simp only [MutualBlock.recName, MutualParts.toBlock]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hmb]
  rfl

/-- **The recogniser settles the pin bit**: `mutualParts?` stores the
structural pin it computed, so the install's `recPinned` guard IS
`mutualRecPinOk` at a recognised block. -/
theorem mutualParts?_recPinned {nPd : Nat} {block : List ConstantInfo} {p : MutualParts}
    (h : mutualParts? nPd block = some p) : p.recPinned = mutualRecPinOk p := by
  unfold mutualParts? at h
  repeat' first
    | (simp only [] at h)
    | (split at h)
  all_goals first
    | (obtain rfl := Option.some.inj h; rfl)
    | (simp at h)

/-! ## The install -/

/-- **The whole core chain**, as the install ran it. -/
theorem checkMutualCore_inv {env envOut : Env} {b : MutualBlock} {F : Nat}
    {streamRecs : Option (List (ConstantVal × List RecRule))}
    (h : checkMutualCore (fueledOps mode F) env b streamRecs = .ok envOut) :
    b.blockNames.Nodup ∧
    (b.formers.all (fun f => f.1.levelParams == b.lps) &&
      b.ctors.all (fun c => c.cv.levelParams == b.lps)) = true ∧
    b.ctors.all (fun c => c.member < b.k) = true ∧
    mutualCtorsGrouped b.ctors = true ∧
    ∃ (env₁ : Env) (fms : List MutualFormerA) (f₀ : MutualFormerA)
      (tq₀ : List Expr × Expr) (ctorsA : List (ConstantVal × Nat))
      (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
      (formers4 : List MutualFormer) (ctors4 : List MutualCtor4)
      (cvRas : List ConstantVal) (rulesOf : List (List (MutualCtor × Expr))),
      mutualFormers (fueledOps mode F) b.nP b.formers env = .ok (env₁, fms) ∧
      fms[0]? = some f₀ ∧
      openPisAtFvars b.nP f₀.cvTa.type 0 = some tq₀ ∧
      mutualCrossChecks (fueledOps mode F) env₁ b.nP f₀ (tq₀.1.map Expr.fvarTypeD) fms
        = .ok () ∧
      b.large = f₀.s.isNeverZero ∧
      checkMutualCtors (fueledOps mode F) env₁ b fms
        (Level.isEquiv f₀.s .zero == some true) b.ctors = .ok (ctorsA, sortss) ∧
      classifyMutualKinds (m := CheckM) b.members3 b.lps b.nP ctorsA = .ok kinds ∧
      mutualFieldsOk env b.members3 b.lps b.nP ctorsA kinds = true ∧
      mutualGenData b fms ctorsA kinds = (formers4, ctors4) ∧
      checkMutualRecTys (fueledOps mode F) (consMutualCtors b.nP ctorsA env₁) b formers4
        ctors4 streamRecs b.k = .ok cvRas ∧
      checkMutualAllRules (m := CheckM)
        (provisionMutualRecs b fms cvRas.zipIdx (consMutualCtors b.nP ctorsA env₁))
        b formers4 ctors4 streamRecs b.k = .ok rulesOf ∧
      mutualTables (m := CheckM) b ctorsA sortss fms.zipIdx
        (storeMutualRecs (consMutualCtors b.nP ctorsA env₁) b fms rulesOf cvRas.zipIdx
          (consMutualCtors b.nP ctorsA env₁)) = .ok envOut := by
  unfold checkMutualCore at h
  simp only at h
  obtain ⟨u₀, hshape, h⟩ := exceptBind_ok h
  obtain ⟨hnd, hlp, hmem, hgr⟩ := mutualShapeOk_inv hshape
  refine ⟨hnd, hlp, hmem, hgr, ?_⟩
  obtain ⟨q₁, hformers, h⟩ := exceptBind_ok h
  obtain ⟨env₁, fms⟩ := q₁
  try simp only at h
  obtain ⟨f₀, hf₀, h⟩ := exceptBind_ok h
  have hf₀' := unwrapOr_ok hf₀
  try simp only at h
  obtain ⟨tq₀, htq₀, h⟩ := exceptBind_ok h
  have htq₀' := unwrapOr_ok htq₀
  try simp only at h
  obtain ⟨u₁, hcross, h⟩ := exceptBind_ok h
  try simp only at h
  by_cases hL : (b.large == f₀.s.isNeverZero) = true
  case neg => rw [if_neg hL] at h; close_throw
  rw [if_pos hL] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨q₂, hctors, h⟩ := exceptBind_ok h
  obtain ⟨ctorsA, sortss⟩ := q₂
  try simp only at h
  obtain ⟨kinds, hkinds, h⟩ := exceptBind_ok h
  try simp only at h
  by_cases hfo : mutualFieldsOk env b.members3 b.lps b.nP ctorsA kinds = true
  case neg => rw [if_neg hfo] at h; close_throw
  rw [if_pos hfo] at h
  try simp only [bind, Except.bind] at h
  generalize hgd : mutualGenData b fms ctorsA kinds = gd at h
  obtain ⟨formers4, ctors4⟩ := gd
  try simp only at h
  obtain ⟨cvRas, hrectys, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨rulesOf, hrules, h⟩ := exceptBind_ok h
  refine ⟨env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4, cvRas, rulesOf,
    hformers, hf₀', htq₀', by cases u₁; exact hcross, beq_iff_eq.mp hL, hctors, hkinds,
    hfo, hgd, hrectys, hrules, h⟩

/-- **The recognised block's install**: the recursor records' pin and
the core. -/
theorem checkMutual_inv {env envOut : Env} {p : MutualParts} {F : Nat}
    (h : checkMutual (fueledOps mode F) env p = .ok envOut) :
    p.recPinned = true ∧
    checkMutualCore (fueledOps mode F) env p.toBlock
      (some (p.members.map fun mb => (mb.cvR, mb.rules))) = .ok envOut := by
  unfold checkMutual at h
  by_cases hp : p.recPinned = true
  case neg => rw [if_neg hp] at h; close_throw
  rw [if_pos hp] at h
  exact ⟨hp, h⟩

end ConLeche
