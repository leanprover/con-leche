import Setlec.Verify.Direct.DirectInv
import Setlec.Kernel.Direct.SumInstall

/-!
# The direct sum install's stage runs, inverted (task #175 sum-types)

Each stage of `checkDirectSum` inverted to the facts the semantic
modules consume: the type former's run, every constructor's run at the
former's environment (`checkDirectSumCtors_inv`, positionally), the
generated recursor's comparison and every generated rule's run
(`checkDirectSumRules_inv`), and the recogniser's pins
(`directSumParts?_inv`).  Shape walks only, as `DirectInv.lean`.
-/

namespace Setlec

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

/-! ## Stage 1: the type former -/

theorem checkDirectSumInd_shape {env envI : Env} {p : DirectSumParts}
    {cvTa : ConstantVal} {F : Nat}
    (h : checkDirectSumInd (fueledOps mode F) env p = .ok (envI, cvTa)) :
    checkConstantVal (fueledOps mode F) env p.cvT = .ok cvTa ∧
    envI = ⟨.indInfo cvTa {} :: env.consts⟩ ∧
    ∃ bs, cvTa.type.stripPis p.nP = some (bs, .sort p.resSort) := by
  unfold checkDirectSumInd at h
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

/-! ## Stage 2: one constructor -/

theorem checkDirectSumCtor_shape {env₀ env : Env} {T : Name} {lps : List Name}
    {nP : Nat} {resSort : Level} {isProp large : Bool} {cvC cvTa cvCa : ConstantVal}
    {nF : Nat} {F : Nat}
    (h : checkDirectSumCtor (fueledOps mode F) env₀ env T lps nP resSort isProp large
      cvC nF cvTa = .ok cvCa) :
    checkConstantVal (fueledOps mode F) env cvC = .ok cvCa ∧
    (∃ cbs, cvCa.type.stripPis (nP + nF) = some (cbs, directFam T lps nP nF)) ∧
    ∃ (fvsP : List Expr) (crest : Expr) (tfvs : List Expr) (trest : Expr)
      (xFvs : List Expr) (sorts : List Level),
      openPisAtFvars nP cvCa.type 0 = some (fvsP, crest) ∧
      openPisAtFvars nP cvTa.type 0 = some (tfvs, trest) ∧
      checkDirectDomsAt (fueledOps mode F) env 0 fvsP
        (tfvs.map Expr.fvarTypeD) nP = .ok () ∧
      openPisAtFvars nF crest nP
        = some (xFvs, Expr.mkAppN (.const T (lps.map .param)) fvsP) ∧
      (∀ x ∈ xFvs, x.fvarTypeD.constsResolve env₀ = true) ∧
      checkDirectFieldSorts (fueledOps mode F) env isProp large resSort
        nP xFvs nF = .ok sorts := by
  unfold checkDirectSumCtor at h
  obtain ⟨cvCa', hccv, h⟩ := exceptBind_ok h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cbs, cbody⟩ := q
  have hq' := unwrapOr_ok hq
  try simp only at h
  by_cases hc : (cbody == directFam T lps nP nF) = true
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
  by_cases h2 : (xrest == Expr.mkAppN (.const T (lps.map .param)) fvsP) = true
  case neg => rw [if_neg h2] at h; close_throw
  rw [if_pos h2] at h
  by_cases h3 : (xFvs.all fun x => Expr.constsResolve env₀ x.fvarTypeD) = true
  case neg => rw [if_neg h3] at h; close_throw
  rw [if_pos h3] at h
  obtain ⟨sorts', hsorts, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨hccv, ⟨cbs, by rw [hq', beq_iff_eq.mp hc]⟩,
    fvsP, crest, tfvs, trest, xFvs, sorts', hcq', htq', by cases u; exact hdoms, ?_,
    ?_, hsorts⟩
  · rw [hxq', beq_iff_eq.mp h2]
  · intro x hx
    exact List.all_eq_true.mp h3 x hx

/-- All constructors, positionally: the annotated list is as long as
the input and every entry is its constructor's run. -/
theorem checkDirectSumCtors_inv {env₀ env : Env} {T : Name} {lps : List Name}
    {nP : Nat} {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal} {F : Nat} :
    ∀ {cs ctorsA : List (ConstantVal × Nat)},
      checkDirectSumCtors (fueledOps mode F) env₀ env T lps nP resSort isProp large
        cvTa cs = .ok ctorsA →
      ctorsA.length = cs.length ∧
      ∀ (j : Nat) (c cA : ConstantVal × Nat), cs[j]? = some c → ctorsA[j]? = some cA →
        cA.2 = c.2 ∧
        checkDirectSumCtor (fueledOps mode F) env₀ env T lps nP resSort isProp large
          c.1 c.2 cvTa = .ok cA.1
  | [], ctorsA, h => by
    simp only [checkDirectSumCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun j c cA hc _ => by simp at hc⟩
  | c :: cs, ctorsA, h => by
    unfold checkDirectSumCtors at h
    obtain ⟨cvCa, hc, h⟩ := exceptBind_ok h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := checkDirectSumCtors_inv hrest
    refine ⟨by simp [hlen], ?_⟩
    intro j c' cA hc' hcA
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc' hcA
      subst hc'; subst hcA
      exact ⟨rfl, hc⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hc' hcA
      exact hall j c' cA hc' hcA

/-! ## Stage 3: the recursor -/

/-- The generated rules, positionally: rule `i` of the run from `j` is
the generator's rule `j + i`, scoped, and inferred. -/
theorem checkDirectSumRules_inv {env : Env} {rlps : List Name} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP : Nat} {tty : Expr}
    {ctors : List (Name × Nat × Expr)} {F : Nat} :
    ∀ {k j : Nat} {rhss : List Expr},
      checkDirectSumRules (fueledOps mode F) env rlps T lps elim large nP tty ctors k j
        = .ok rhss →
      rhss.length = k ∧
      ∀ i, i < k → ∃ rhs, rhss[i]? = some rhs ∧
        directRecRhs T lps elim large nP tty ctors (j + i) = some rhs ∧
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
      have hgen' : directRecRhs T lps elim large nP tty ctors (j + (i + 1)) = some rhs' := by
        rw [show j + (i + 1) = j + 1 + i from by omega]; exact hgen
      exact ⟨rhs', hget', hgen', hlp, hres, hbv, hfv, hty⟩

theorem checkDirectSumRec_shape {env : Env} {p : DirectSumParts}
    {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {F : Nat}
    (h : checkDirectSumRec (fueledOps mode F) env p cvTa ctorsA = .ok (cvRa, rhss)) :
    ∃ (cvRi : ConstantVal) (recTy sty : Expr) (u : Level),
      checkConstantVal (fueledOps mode F) env p.cvR = .ok cvRi ∧
      directRecTy p.cvT.name p.cvT.levelParams p.elim p.large p.nP cvTa.type
        (ctorsA.map fun c => (c.1.name, c.2, c.1.type)) = some recTy ∧
      recTy.allLevelParamsDefined p.cvR.levelParams = true ∧
      recTy.constsResolve env = true ∧
      recTy.looseBVarsBounded 0 = true ∧ recTy.hasFvar = false ∧
      inferTypeCore mode env F 0 recTy = .ok sty ∧
      ensureSortCore mode env F 0 sty = .ok u ∧
      isDefEqCore mode env F 0 cvRi.type recTy = .ok true ∧
      checkDirectSumRules (fueledOps mode F) env p.cvR.levelParams p.cvT.name
        p.cvT.levelParams p.elim p.large p.nP cvTa.type
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

theorem directSumPartsCore?_inv {block : List ConstantInfo} {p : DirectSumParts}
    (h : directSumPartsCore? block = some p) :
    p.isProp = (Level.isEquiv p.resSort .zero == some true) ∧
    p.cvR.name = p.cvT.name.str "rec" ∧
    p.ctors.length ≠ 1 ∧
    (∀ c ∈ p.ctors, c.1.levelParams = p.cvT.levelParams ∧
      reservedBasisNames.contains c.1.name = false) ∧
    reservedBasisNames.contains p.cvT.name = false ∧
    reservedBasisNames.contains p.cvR.name = false ∧
    (p.large = true → p.elim ∈ p.cvR.levelParams) ∧
    p.rhss.length = p.ctors.length := by
  unfold directSumPartsCore? at h
  split at h
  · next cvT caps rest =>
    split at h
    · next cs cvR mI rP rules hsplit =>
      try dsimp only at h
      split at h
      · exact nomatch h
      · next hn1 =>
        try dsimp only at h
        split at h
        · next hc =>
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
          cases hstripP : Expr.stripPis (rP - (cs.length + 1)) cvT.type with
          | none => rw [hstripP] at h; exact nomatch h
          | some q =>
            obtain ⟨fstP, body⟩ := q
            rw [hstripP] at h
            cases body
            case sort s =>
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
              have hn1' : (cs.map (fun c => (c.1, c.2.2))).length ≠ 1 := by
                rw [List.length_map]
                intro h1
                apply hn1
                simp [h1]
              split at h
              · next lq elim' hlarge =>
                obtain rfl := Option.some.inj h
                refine ⟨rfl, hc.1.1.1.1.1, hn1', hcs, hc.1.1.1.2, hc.1.1.2, ?_, ?_⟩
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
                · obtain rfl := Option.some.inj h
                  refine ⟨rfl, hc.1.1.1.1.1, hn1', hcs, hc.1.1.1.2, hc.1.1.2, ?_, ?_⟩
                  · intro hl
                    exact absurd hl Bool.false_ne_true
                  · simp [hrules]
                · exact nomatch h
            all_goals first | exact nomatch h | simp at h
        · exact nomatch h
    · exact nomatch h
  · exact nomatch h

theorem directSumParts?_inv {env : Env} {block : List ConstantInfo} {p : DirectSumParts}
    (h : directSumParts? env block = some p) :
    p.isProp = (Level.isEquiv p.resSort .zero == some true) ∧
    p.cvR.name = p.cvT.name.str "rec" ∧
    p.ctors.length ≠ 1 ∧
    (∀ c ∈ p.ctors, c.1.levelParams = p.cvT.levelParams ∧
      reservedBasisNames.contains c.1.name = false) ∧
    reservedBasisNames.contains p.cvT.name = false ∧
    reservedBasisNames.contains p.cvR.name = false ∧
    (p.large = true → p.elim ∈ p.cvR.levelParams) ∧
    p.rhss.length = p.ctors.length := by
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

end Setlec
