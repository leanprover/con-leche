import Setlec.Verify.Direct.DirectWF

/-!
# The direct install's stage runs, inverted to their records (task #175 W4c, P3)

Each stage of `checkDirectStruct` is a `do`-block of guards and
operation runs; the P install reads those runs (the annotated types'
inference, the definitional pins at the opened frames, the field
sorts) as its premises.  This module inverts every stage into exactly
the facts the semantic modules consume — named runs, at the frames
the checker ran them.  Shape walks only: `exceptBind_ok` per bind,
`rw [if_pos …]` per guard (BridgeWfImp's idiom — the do-notation's
join points defeat a bare `split`), `close_throw` on the failing
branches.
-/

namespace Setlec

variable {mode : CheckMode}

private theorem dThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact dThrow_ne_ok (by assumption))
        | (exfalso; exact dThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-! ## Stage 1: the type former -/

theorem checkDirectInd_shape {env envI : Env} {p : DirectParts}
    {cvTa : ConstantVal} {F : Nat}
    (h : checkDirectInd (fueledOps mode F) env p = .ok (envI, cvTa)) :
    checkConstantVal (fueledOps mode F) env p.cvT = .ok cvTa ∧
    envI = ⟨.indInfo cvTa (directCaps p) :: env.consts⟩ ∧
    ∃ bs, cvTa.type.stripPis p.nP = some (bs, .sort p.resSort) := by
  unfold checkDirectInd at h
  obtain ⟨cvTa', hccv, h⟩ := exceptBind_ok h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨bs, tbody⟩ := q
  have hq' := unwrapOr_ok hq
  try simp only at h
  by_cases hc : (tbody == Expr.sort p.resSort) = true
  · rw [if_pos hc] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hccv, rfl, bs, by rw [hq', beq_iff_eq.mp hc]⟩
  · rw [if_neg hc] at h
    close_throw

/-! ## Stage 2: the constructor -/

theorem checkDirectCtor_shape {env₀ env envC : Env} {p : DirectParts}
    {cvTa cvCa : ConstantVal} {sorts : List Level} {F : Nat}
    (h : checkDirectCtor (fueledOps mode F) env₀ env p cvTa
      = .ok (envC, cvCa, sorts)) :
    checkConstantVal (fueledOps mode F) env p.cvC = .ok cvCa ∧
    envC = ⟨.ctorInfo cvCa p.nP p.nF :: env.consts⟩ ∧
    (∃ cbs, cvCa.type.stripPis (p.nP + p.nF)
      = some (cbs, directFam p.cvT.name p.cvT.levelParams p.nP p.nF)) ∧
    ∃ (fvsP : List Expr) (crest : Expr) (tfvs : List Expr) (trest : Expr)
      (xFvs : List Expr),
      openPisAtFvars p.nP cvCa.type 0 = some (fvsP, crest) ∧
      openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest) ∧
      checkDirectDomsAt (fueledOps mode F) env 0 fvsP
        (tfvs.map Expr.fvarTypeD) p.nP = .ok () ∧
      openPisAtFvars p.nF crest p.nP
        = some (xFvs, Expr.mkAppN (.const p.cvT.name
            (p.cvT.levelParams.map .param)) fvsP) ∧
      (∀ x ∈ xFvs, x.fvarTypeD.constsResolve env₀ = true) ∧
      checkDirectFieldSorts (fueledOps mode F) env p.isProp p.large p.resSort
        p.nP xFvs p.nF = .ok sorts := by
  unfold checkDirectCtor at h
  obtain ⟨cvCa', hccv, h⟩ := exceptBind_ok h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cbs, cbody⟩ := q
  have hq' := unwrapOr_ok hq
  try simp only at h
  by_cases hc : (cbody == directFam p.cvT.name p.cvT.levelParams p.nP p.nF) = true
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
  by_cases h2 : (xrest == Expr.mkAppN (.const p.cvT.name
      (p.cvT.levelParams.map .param)) fvsP) = true
  case neg => rw [if_neg h2] at h; close_throw
  rw [if_pos h2] at h
  by_cases h3 : (xFvs.all fun x => Expr.constsResolve env₀ x.fvarTypeD) = true
  case neg => rw [if_neg h3] at h; close_throw
  rw [if_pos h3] at h
  obtain ⟨sorts', hsorts, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨hccv, rfl, ⟨cbs, by rw [hq', beq_iff_eq.mp hc]⟩,
    fvsP, crest, tfvs, trest, xFvs, hcq', htq', by cases u; exact hdoms, ?_,
    ?_, hsorts⟩
  · rw [hxq', beq_iff_eq.mp h2]
  · intro x hx
    exact List.all_eq_true.mp h3 x hx

/-! ## Stage 3: the recursor's type -/

theorem checkDirectRecTy_shape {env : Env} {p : DirectParts}
    {cvTa cvCa cvRa : ConstantVal} {F : Nat}
    (h : checkDirectRecTy (fueledOps mode F) env p cvTa cvCa cvRa = .ok ()) :
    directShape p.cvT.name p.cvC.name p.cvT.levelParams p.elim p.large
      p.nP p.nF cvTa.type cvCa.type cvRa.type = true ∧
    ∃ (fvsP : List Expr) (rest : Expr) (cdomsP : List Expr) (crest : Expr)
      (mfv : Expr) (mbs : List (Name × Expr × BinderMeta)) (mdom : Expr)
      (minfv : Expr) (xFvs : List Expr) (minBody : Expr)
      (cdomsF : List Expr) (crest2 : Expr)
      (jbs : List (Name × Expr × BinderMeta)) (jbody jdom : Expr),
      openPisAtFvars (p.nP + 2) cvRa.type 0 = some (fvsP, rest) ∧
      Expr.instPisAt (fvsP.take p.nP) cvCa.type = some (cdomsP, crest) ∧
      checkDirectDomsAt (fueledOps mode F) env 0 (fvsP.take p.nP) cdomsP p.nP
        = .ok () ∧
      fvsP[p.nP]? = some mfv ∧
      mfv.fvarTypeD.stripPis 1
        = some (mbs, .sort (if p.large then .param p.elim else .zero)) ∧
      (mbs[0]?).map (·.2.1) = some mdom ∧
      isDefEqCore mode env F p.nP mdom
        (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
          (fvsP.take p.nP)) = .ok true ∧
      fvsP[p.nP + 1]? = some minfv ∧
      openPisAtFvars p.nF minfv.fvarTypeD (p.nP + 2) = some (xFvs, minBody) ∧
      Expr.instPisAt xFvs crest = some (cdomsF, crest2) ∧
      checkDirectDomsAt (fueledOps mode F) env (p.nP + 2) xFvs cdomsF p.nF
        = .ok () ∧
      crest2 = Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (fvsP.take p.nP) ∧
      minBody = Expr.app mfv
        (Expr.mkAppN (.const p.cvC.name (p.cvT.levelParams.map .param))
          (fvsP.take p.nP ++ xFvs)) ∧
      rest.stripPis 1 = some (jbs, jbody) ∧
      (jbs[0]?).map (·.2.1) = some jdom ∧
      isDefEqCore mode env F (p.nP + 2) jdom
        (Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
          (fvsP.take p.nP)) = .ok true ∧
      jbody = Expr.app mfv (.bvar 0) := by
  unfold checkDirectRecTy at h
  try simp only at h
  by_cases h0 : directShape p.cvT.name p.cvC.name p.cvT.levelParams p.elim
      p.large p.nP p.nF cvTa.type cvCa.type cvRa.type = true
  case neg => rw [if_neg h0] at h; close_throw
  rw [if_pos h0] at h
  obtain ⟨q, hop, h⟩ := exceptBind_ok h
  obtain ⟨fvsP, rest⟩ := q
  have hop' := unwrapOr_ok hop
  try simp only at h
  obtain ⟨q2, hci, h⟩ := exceptBind_ok h
  obtain ⟨cdomsP, crest⟩ := q2
  have hci' := unwrapOr_ok hci
  try simp only at h
  obtain ⟨u1, hd1, h⟩ := exceptBind_ok h
  obtain ⟨mfv, hmf, h⟩ := exceptBind_ok h
  have hmf' := unwrapOr_ok hmf
  obtain ⟨q3, hms, h⟩ := exceptBind_ok h
  obtain ⟨mbs, mbody⟩ := q3
  have hms' := unwrapOr_ok hms
  try simp only at h
  obtain ⟨mdom, hmd, h⟩ := exceptBind_ok h
  have hmd' := unwrapOr_ok hmd
  obtain ⟨b1, hb1, h⟩ := exceptBind_ok h
  cases b1 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    close_throw
  | true =>
  rw [if_pos rfl] at h
  try simp only at h
  by_cases h2 : (mbody == Expr.sort (if p.large then .param p.elim else .zero))
      = true
  case neg => rw [if_neg h2] at h; close_throw
  rw [if_pos h2] at h
  obtain ⟨minfv, hmi, h⟩ := exceptBind_ok h
  have hmi' := unwrapOr_ok hmi
  obtain ⟨q4, hox, h⟩ := exceptBind_ok h
  obtain ⟨xFvs, minBody⟩ := q4
  have hox' := unwrapOr_ok hox
  try simp only at h
  obtain ⟨q5, hcf, h⟩ := exceptBind_ok h
  obtain ⟨cdomsF, crest2⟩ := q5
  have hcf' := unwrapOr_ok hcf
  try simp only at h
  obtain ⟨u2, hd2, h⟩ := exceptBind_ok h
  by_cases h3 : (crest2 == Expr.mkAppN (.const p.cvT.name
      (p.cvT.levelParams.map .param)) (fvsP.take p.nP)) = true
  case neg => rw [if_neg h3] at h; close_throw
  rw [if_pos h3] at h
  by_cases h4 : (minBody == Expr.app mfv
      (Expr.mkAppN (.const p.cvC.name (p.cvT.levelParams.map .param))
        (fvsP.take p.nP ++ xFvs))) = true
  case neg => rw [if_neg h4] at h; close_throw
  rw [if_pos h4] at h
  obtain ⟨q6, hjs, h⟩ := exceptBind_ok h
  obtain ⟨jbs, jbody⟩ := q6
  have hjs' := unwrapOr_ok hjs
  try simp only at h
  obtain ⟨jdom, hjd, h⟩ := exceptBind_ok h
  have hjd' := unwrapOr_ok hjd
  obtain ⟨b2, hb2, h⟩ := exceptBind_ok h
  cases b2 with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    close_throw
  | true =>
  rw [if_pos rfl] at h
  try simp only at h
  by_cases h5 : (jbody == Expr.app mfv (.bvar 0)) = true
  case neg => rw [if_neg h5] at h; close_throw
  refine ⟨h0, fvsP, rest, cdomsP, crest, mfv, mbs, mdom, minfv, xFvs, minBody,
    cdomsF, crest2, jbs, jbody, jdom, hop', hci', by cases u1; exact hd1, hmf',
    by rw [hms', beq_iff_eq.mp h2], hmd', hb1, hmi', hox', hcf',
    by cases u2; exact hd2, beq_iff_eq.mp h3, beq_iff_eq.mp h4, hjs', hjd',
    hb2, beq_iff_eq.mp h5⟩

/-! ## Stage 4: the rule -/

theorem checkDirectRule_shape {env : Env} {p : DirectParts}
    {cvCa cvRa : ConstantVal} {rhsA : Expr} {F : Nat}
    (h : checkDirectRule (fueledOps mode F) env p cvCa cvRa = .ok rhsA) :
    p.rhs.hasFvar = false ∧ p.rhs.looseBVarsBounded 0 = true ∧
    annotateCore mode env F 0 p.rhs = .ok rhsA ∧
    rhsA.allLevelParamsDefined cvRa.levelParams = true ∧
    rhsA.constsResolve env = true ∧ rhsA.looseBVarsBounded 0 = true ∧
    rhsA.hasFvar = false ∧
    (∃ rbs, rhsA.stripLams (p.nP + 2 + p.nF) = some (rbs, directRuleBody p.nF)) ∧
    ∃ (fvsP : List Expr) (rrest : Expr) (cdomsP : List Expr) (crest : Expr)
      (xFvs : List Expr) (xrest : Expr) (ldoms : List Expr) (lrest rhsTy : Expr),
      openPisAtFvars (p.nP + 2) cvRa.type 0 = some (fvsP, rrest) ∧
      Expr.instPisAt (fvsP.take p.nP) cvCa.type = some (cdomsP, crest) ∧
      openPisAtFvars p.nF crest (p.nP + 2) = some (xFvs, xrest) ∧
      Expr.instLamsAt (fvsP ++ xFvs) rhsA = some (ldoms, lrest) ∧
      checkDefEqList (fueledOps mode F) env (p.nP + 2 + p.nF)
        ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms = .ok () ∧
      inferTypeCore mode env F 0 rhsA = .ok rhsTy := by
  unfold checkDirectRule at h
  try simp only at h
  by_cases h0 : (!p.rhs.hasFvar && Expr.looseBVarsBounded 0 p.rhs) = true
  case neg => rw [if_neg h0] at h; close_throw
  rw [if_pos h0] at h
  obtain ⟨rhsA', hann, h⟩ := exceptBind_ok h
  try simp only at h
  by_cases h1 : (Expr.allLevelParamsDefined cvRa.levelParams rhsA' &&
      Expr.constsResolve env rhsA' && Expr.looseBVarsBounded 0 rhsA' &&
      !rhsA'.hasFvar) = true
  case neg => rw [if_neg h1] at h; close_throw
  rw [if_pos h1] at h
  obtain ⟨q, hsl, h⟩ := exceptBind_ok h
  obtain ⟨rbs, rbody⟩ := q
  have hsl' := unwrapOr_ok hsl
  try simp only at h
  by_cases h2 : (rbody == directRuleBody p.nF) = true
  case neg => rw [if_neg h2] at h; close_throw
  rw [if_pos h2] at h
  obtain ⟨q2, hop, h⟩ := exceptBind_ok h
  obtain ⟨fvsP, rrest⟩ := q2
  have hop' := unwrapOr_ok hop
  try simp only at h
  obtain ⟨q3, hci, h⟩ := exceptBind_ok h
  obtain ⟨cdomsP, crest⟩ := q3
  have hci' := unwrapOr_ok hci
  try simp only at h
  obtain ⟨q4, hox, h⟩ := exceptBind_ok h
  obtain ⟨xFvs, xrest⟩ := q4
  have hox' := unwrapOr_ok hox
  try simp only at h
  obtain ⟨q5, hli, h⟩ := exceptBind_ok h
  obtain ⟨ldoms, lrest⟩ := q5
  have hli' := unwrapOr_ok hli
  try simp only at h
  obtain ⟨u, hdl, h⟩ := exceptBind_ok h
  obtain ⟨rhsTy, hty, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h0 h1
  exact ⟨h0.1, h0.2, hann, h1.1.1.1, h1.1.1.2, h1.1.2, h1.2,
    ⟨rbs, by rw [hsl', beq_iff_eq.mp h2]⟩,
    fvsP, rrest, cdomsP, crest, xFvs, xrest, ldoms, lrest, rhsTy,
    hop', hci', hox', hli', by cases u; exact hdl, hty⟩

/-! ## The frame walks: binder-domain pins and field sorts -/

/-- `checkDirectDomsAt`, inverted: every position below the walk's
bound carries a successful `isDefEqCore` at its own frame. -/
theorem checkDirectDomsAt_inv {env : Env} {F off : Nat} {fvs doms : List Expr} :
    ∀ {j : Nat},
      checkDirectDomsAt (fueledOps mode F) env off fvs doms j = .ok () →
      ∀ i, i < j → ∃ a b, fvs[i]? = some a ∧ doms[i]? = some b ∧
        isDefEqCore mode env F (off + i) (Expr.fvarTypeD a) b = .ok true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | j + 1, h, i, hi => by
    unfold checkDirectDomsAt at h
    obtain ⟨a, ha, h⟩ := exceptBind_ok h
    have ha' := unwrapOr_ok ha
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    have hb' := unwrapOr_ok hb
    try simp only at h
    obtain ⟨c, hc, h⟩ := exceptBind_ok h
    have hc' : isDefEqCore mode env F (off + j) (Expr.fvarTypeD a) b = .ok c := hc
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      close_throw
    | true =>
    rw [if_pos rfl] at h
    try simp only at h
    rcases Nat.lt_or_ge i j with hij | hij
    · exact checkDirectDomsAt_inv h i hij
    · obtain rfl : i = j := by omega
      exact ⟨a, b, ha', hb', hc'⟩

/-- `checkDirectFieldSorts`, inverted: the sorts are returned in field
order, one per field, each the `ensureSort` of the field annotation's
inferred type at the field's own frame, under the official universe
bound (`isProp = false`) or the large-eliminator propositionality
re-check (`isProp ∧ large`). -/
theorem checkDirectFieldSorts_inv {env : Env} {isProp large : Bool}
    {s : Level} {nP F : Nat} {fvs : List Expr} :
    ∀ {j : Nat} {sorts : List Level},
      checkDirectFieldSorts (fueledOps mode F) env isProp large s nP fvs j
        = .ok sorts →
      sorts.length = j ∧
      ∀ i, i < j → ∃ fv ty u, fvs[i]? = some fv ∧ sorts[i]? = some u ∧
        inferTypeCore mode env F (nP + i) (Expr.fvarTypeD fv) = .ok ty ∧
        ensureSortCore mode env F (nP + i) ty = .ok u ∧
        (isProp = false → Level.leq u s = some true) ∧
        (isProp = true → large = true →
          (Level.isEquiv u .zero == some true) = true)
  | 0, sorts, h => by
    simp only [checkDirectFieldSorts, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | j + 1, sorts, h => by
    unfold checkDirectFieldSorts at h
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
        checkDirectFieldSorts (fueledOps mode F) env isProp large s nP fvs j
          = .ok rest ∧ sorts = rest ++ [u] ∧
        (isProp = false → Level.leq u s = some true) ∧
        (isProp = true → large = true →
          (Level.isEquiv u .zero == some true) = true) by
      obtain ⟨rest, hrest, rfl, hleq, hz⟩ := hs
      obtain ⟨hlen, hall⟩ := checkDirectFieldSorts_inv hrest
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
        | none => rw [hl] at hb; exact absurd hb (by simp [liftFueled, throw, throwThe, MonadExceptOf.throw])
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
        by_cases hz : (Level.isEquiv u .zero == some true) = true
        · rw [if_pos hz] at h
          simp only [pure, Except.pure, bind, Except.bind] at h
          obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
          simp only [Except.ok.injEq] at h
          refine ⟨rest, hrest, h.symm, fun h0 => ?_, fun _ _ => hz⟩
          rw [hp] at h0
          exact nomatch h0
        · rw [if_neg hz] at h
          close_throw
      · rw [if_neg hl] at h
        simp only [pure, Except.pure, bind, Except.bind] at h
        obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
        simp only [Except.ok.injEq] at h
        refine ⟨rest, hrest, h.symm, fun h0 => ?_, fun _ h1 => absurd h1 hl⟩
        rw [hp] at h0
        exact nomatch h0

end Setlec
