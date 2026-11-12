module

public import ConLeche.Verify.BridgeWfImp
public import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Extend.Inversions
import ConLeche.Kernel.Inductives.SumInstall

public section

/-!
# The per-member stage runs of the block install, inverted

The stages `checkBlock` runs per member (`checkSumTele`,
`checkSumCtors`, the field-sort and domain walks, the projection
table) inverted to their records, and environment well-formedness
across their conses.  Every fact is read off the stage's own guards:
each stored constant was checked closed, level-defined, resolving and
bound *by the stage itself*, so the inversions here are shape walks
(`exceptBind_ok` / `split`) that keep exactly those guards.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A thrown step never succeeds. -/
theorem structThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The shape walk's closers: every non-surviving goal holds a
`throw … = .ok _` (possibly under a join point's zeta step). -/
local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact structThrow_ne_ok (by assumption))
        | (exfalso; exact structThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-- A successful `unwrapOr` names its option. -/
theorem unwrapOr_ok {α : Type} {x : Option α} {e : CheckError} {a : α}
    (h : (unwrapOr x e : CheckM α) = .ok a) : x = some a := by
  cases x with
  | none => exact absurd h (by simp [unwrapOr, throw, throwThe, MonadExceptOf.throw])
  | some b =>
    simp only [unwrapOr, pure, Except.pure, Except.ok.injEq] at h
    rw [h]

/-- Introduction for `ConstWF` with the clause types spelled out (the
`thmInfo` clause defaulted, as every constant installed by the block
install is an inductive-kind one). -/
theorem structConstWF {env : Env} {c : ConstantInfo}
    (h1 : c.toConstantVal.type.hasFvar = false)
    (h2 : c.toConstantVal.type.allLevelParamsDefined
      c.toConstantVal.levelParams = true)
    (h3 : c.toConstantVal.type.constsResolve env = true)
    (h4 : c.toConstantVal.type.looseBVarsBounded 0 = true)
    (h5 : ∀ cv value hint, c = .defnInfo cv value hint →
      value.hasFvar = false ∧
      value.allLevelParamsDefined cv.levelParams = true ∧
      value.constsResolve env = true ∧
      value.looseBVarsBounded 0 = true)
    (h6 : ∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules →
      ∀ r, r ∈ rules →
        (RecRule.rhs r).hasFvar = false ∧
        (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
        (RecRule.rhs r).constsResolve env = true ∧
        (RecRule.rhs r).looseBVarsBounded 0 = true ∧
        ∀ lvls pins, RecRule.fire r = .nested lvls pins →
          NestedRead (·.constsResolve env) cv.levelParams cv.type mI rP pins.length lvls pins) :
    ConstWF env c := ⟨h1, h2, h3, h4, h5, h6⟩

/-! ## The projection table (#175) -/

/-- The table stage's run, inverted: the bodies pass the scoping guard, the structure is stored and
has no table yet. -/
theorem checkStructProjTable_inv {env : Env} {t : ProjTable}
    (h : checkStructProjTable (m := CheckM) t env = .ok ()) :
    (t.bodies.size = t.numFields ∧ t.bodies.all (fun b => !b.hasFvar &&
        b.allLevelParamsDefined t.levelParams && b.constsResolve env &&
        b.looseBVarsBounded (t.numParams + 1)) = true) ∧
      (env.find? t.structName).isSome = true ∧ env.findTable? t.structName = none := by
  unfold checkStructProjTable at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exceptBind_ok h)
    | split at h
  all_goals first
    | exact ⟨by assumption, by assumption, Option.isNone_iff_eq_none.mp (by assumption)⟩
    | close_throw

/-- **A table's checks at a later environment**: the structure and everything the bodies mention
are still stored there, and the structure still has no table. -/
theorem checkStructProjTable_mono {env env' : Env} {t : ProjTable}
    (hfind : ∀ n ci, env.find? n = some ci → env'.find? n = some ci)
    (hT : env'.findTable? t.structName = none)
    (h : checkStructProjTable (m := CheckM) t env = .ok ()) :
    checkStructProjTable (m := CheckM) t env' = .ok () := by
  obtain ⟨⟨hsize, hall⟩, hTs, -⟩ := checkStructProjTable_inv h
  have hall' : t.bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined t.levelParams && b.constsResolve env' &&
      b.looseBVarsBounded (t.numParams + 1)) = true := by
    refine Array.all_eq_true_iff_forall_mem.mpr fun b hbm => ?_
    have hb' := (Array.all_eq_true_iff_forall_mem.mp hall) b hbm
    simp only [Bool.and_eq_true] at hb' ⊢
    refine ⟨⟨hb'.1.1, Expr.constsResolve_of_find (fun n hn => ?_) hb'.1.2⟩, hb'.2⟩
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    rw [hfind _ _ hci]
    rfl
  have hTs' : (env'.find? t.structName).isSome = true := by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hTs
    rw [hfind _ _ hci]
    rfl
  unfold checkStructProjTable
  simp only [pure, Except.pure, bind, Except.bind]
  rw [ite_eq_left ⟨hsize, hall'⟩, ite_eq_left hTs', ite_eq_left (by rw [hT]; rfl)]

/-- **A projection table's check makes the table well formed** where it ran. -/
theorem checkStructProjTable_tableWF {env : Env} {t : ProjTable}
    (h : checkStructProjTable (m := CheckM) t env = .ok ()) : TableWF env t := by
  obtain ⟨⟨hsize, hall⟩, hT, -⟩ := checkStructProjTable_inv h
  refine ⟨hT, hsize, fun i b hb => ?_⟩
  have hmem : b ∈ t.bodies := Array.mem_of_getElem? hb
  have hb' := (Array.all_eq_true_iff_forall_mem.mp hall) b hmem
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hb'
  exact ⟨hb'.1.1.1, hb'.1.1.2, hb'.1.2, hb'.2⟩

/-- A table the stage checked keeps an environment well-formed. -/
theorem direct_table_wf {env : Env} (henv : EnvWF env) {t : ProjTable}
    (h : checkStructProjTable (m := CheckM) t env = .ok ()) :
    EnvWF ⟨env.consts, t :: env.tables⟩ :=
  EnvWF.pushTable henv (checkStructProjTable_tableWF h)


/-! ## The block's tables -/

/-- **A block's tables at a structure-like member**: its table, read off its constructor, then the
rest's. -/
theorem blockTables_cons_some {p : BlockShape} {ms : MemberShape} {rest : List MemberShape}
    {c : ConstantVal × Nat} (hc : ms.structCtor? = some c) {Q : List ProjTable}
    (h : blockTables p (ms :: rest) = some Q) :
    ∃ bodies Qr, structProjBodies ms.declared.name p.nP c.2 c.1.type = some bodies ∧
      blockTables p rest = some Qr ∧
      Q = ⟨ms.declared.name, p.lps, p.nP, c.1.name, c.2, bodies⟩ :: Qr := by
  simp only [blockTables, hc] at h
  obtain ⟨bodies, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Qr, hQr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨bodies, Qr, hb, hQr, rfl⟩

/-- A block's tables at any other member: the rest's. -/
theorem blockTables_cons_none {p : BlockShape} {ms : MemberShape} {rest : List MemberShape}
    (hc : ms.structCtor? = none) : blockTables p (ms :: rest) = blockTables p rest := by
  simp only [blockTables, hc]

/-- Every table of a block is at a member's declared name. -/
theorem blockTables_names (p : BlockShape) :
    ∀ (l : List MemberShape) (Q : List ProjTable), blockTables p l = some Q →
      ∀ t ∈ Q, ∃ ms ∈ l, t.structName = ms.declared.name
  | [], Q, h, t, ht => by
    simp only [blockTables, Option.some.injEq] at h
    subst h
    nomatch ht
  | ms :: rest, Q, h, t, ht => by
    have hrest : ∀ Qr, blockTables p rest = some Qr → t ∈ Qr →
        ∃ m ∈ ms :: rest, t.structName = m.declared.name := fun Qr hQr hr => by
      obtain ⟨m, hm, hn⟩ := blockTables_names p rest Qr hQr t hr
      exact ⟨m, List.mem_cons_of_mem _ hm, hn⟩
    cases hc : ms.structCtor? with
    | none => exact hrest Q (by rw [← blockTables_cons_none hc]; exact h) ht
    | some c =>
      obtain ⟨bodies, Qr, -, hQr, rfl⟩ := blockTables_cons_some hc h
      rcases List.mem_cons.mp ht with rfl | hr
      · exact ⟨ms, List.mem_cons_self, rfl⟩
      · exact hrest Qr hQr hr

/-! ## The frame walks: binder-domain pins and field sorts -/

/-- `checkStructDomsAt`, inverted: every position below the walk's
bound carries a successful `isDefEqCore` at its own frame. -/
theorem checkStructDomsAt_inv {env : Env} {F off : Nat} {fvs doms : List Expr} :
    ∀ {j : Nat},
      checkStructDomsAt (fueledOps mode F) env off fvs doms j = .ok () →
      ∀ i, i < j → ∃ a b, fvs[i]? = some a ∧ doms[i]? = some b ∧
        isDefEqCore mode false env F (off + i) (Expr.fvarTypeD a) b = .ok true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | j + 1, h, i, hi => by
    unfold checkStructDomsAt at h
    obtain ⟨a, ha, h⟩ := exceptBind_ok h
    have ha' := unwrapOr_ok ha
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    have hb' := unwrapOr_ok hb
    try simp only at h
    obtain ⟨c, hc, h⟩ := exceptBind_ok h
    have hc' : isDefEqCore mode false env F (off + j) (Expr.fvarTypeD a) b = .ok c := hc
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      close_throw
    | true =>
    rw [ite_eq_left rfl] at h
    try simp only at h
    rcases Nat.lt_or_ge i j with hij | hij
    · exact checkStructDomsAt_inv h i hij
    · obtain rfl : i = j := by omega
      exact ⟨a, b, ha', hb', hc'⟩


/-!
## The constructor-list stages, inverted

Every stage carries the index count `nIdx` (#175): the constructor's
residual is the family at the parameters followed by `nIdx` index
expressions (`structCtorResidOk`, inverted by `residual_shape`), and
the field-sort walk `checkStructFieldSortsI`'s large-eliminator clause
admits a non-propositional field that is one of the index expressions.
-/


/-! ## The residual test, inverted -/

/-- The head/arity/parameter-prefix test that `structCtorResidOk` and
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

/-- `checkSumTele`, inverted. -/
theorem checkSumTele_shape {n : Nat} {cvTa₀ cvTa : ConstantVal} {s : Level}
    (h : (checkSumTele n cvTa₀ : CheckM _) = .ok (cvTa, s)) :
    cvTa = cvTa₀ ∧ ∃ bs, cvTa₀.type.stripPis n = some (bs, .sort s) := by
  unfold checkSumTele at h
  split at h
  · next bs s' hst =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, bs, hst⟩
  · exact nomatch h

/-! ## Stage 2: one constructor -/

/-- **The fields' sorts at an accepting walk**: one per field, in field order, each the `ensureSort` of
the field domain's inferred type at the field's own frame, under
the official universe bound (`isProp = false`) or — at a large
eliminator on a `Prop` family — the subsingleton-elimination criterion:
the field is a proposition OR one of the residual's index expressions. -/
abbrev FieldSorts (mode : CheckMode) (F : Nat) (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) (j : Nat) (sorts : List Level) : Prop :=
  sorts.length = j ∧
  ∀ i, i < j → ∃ fv ty u, fvs[i]? = some fv ∧ sorts[i]? = some u ∧
    inferTypeCore mode false env F (nP + i) (Expr.fvarTypeD fv) = .ok ty ∧
    ensureSortCore mode false env F (nP + i) ty = .ok u ∧
    (isProp = false → Level.leq u s = some true) ∧
    (isProp = true → large = true →
      (Level.isEquiv u .zero == some true) = true ∨ idxArgs.contains fv = true)

/-- `checkStructFieldSortsI`, inverted: an accepting walk has its fields' sorts. -/
theorem checkStructFieldSortsI_inv {env : Env} {isProp large : Bool}
    {s : Level} {nP F : Nat} {fvs idxArgs : List Expr} :
    ∀ {j : Nat},
      checkStructFieldSortsI (fueledOps mode F) env isProp large s nP fvs idxArgs j = .ok () →
      ∃ sorts, FieldSorts mode F env isProp large s nP fvs idxArgs j sorts
  | 0, _ => ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | j + 1, h => by
    unfold checkStructFieldSortsI at h
    obtain ⟨fv, hfv, h⟩ := exceptBind_ok h
    have hfv' := unwrapOr_ok hfv
    try simp only at h
    obtain ⟨ty, hty₀, h⟩ := exceptBind_ok h
    have hty : inferTypeCore mode false env F (nP + j) (Expr.fvarTypeD fv) = .ok ty := hty₀
    obtain ⟨u, hu₀, h⟩ := exceptBind_ok h
    have hu : ensureSortCore mode false env F (nP + j) ty = .ok u := hu₀
    try simp only at h
    -- the guard, as one fact per branch
    suffices hs :
        checkStructFieldSortsI (fueledOps mode F) env isProp large s nP fvs idxArgs j = .ok () ∧
        (isProp = false → Level.leq u s = some true) ∧
        (isProp = true → large = true →
          (Level.isEquiv u .zero == some true) = true ∨ idxArgs.contains fv = true) by
      obtain ⟨hrest, hleq, hz⟩ := hs
      obtain ⟨rest, hlen, hall⟩ := checkStructFieldSortsI_inv hrest
      refine ⟨rest ++ [u], by simp [hlen], ?_⟩
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
    · rw [ite_eq_left hnp] at h
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
      rw [ite_eq_left rfl] at h
      refine ⟨h, fun _ => hb', fun hp => ?_⟩
      simp [hp] at hnp
    · rw [ite_eq_right hnp] at h
      have hp : isProp = true := by simpa using hnp
      by_cases hl : large = true
      · rw [ite_eq_left hl] at h
        by_cases hz : (Level.isEquiv u .zero == some true || idxArgs.contains fv) = true
        · rw [ite_eq_left hz] at h
          refine ⟨h, fun h0 => ?_, fun _ _ => ?_⟩
          · rw [hp] at h0
            exact nomatch h0
          · exact Bool.or_eq_true_iff.mp hz
        · rw [ite_eq_right hz] at h
          close_throw
      · rw [ite_eq_right hl] at h
        refine ⟨h, fun h0 => ?_, fun _ h1 => absurd h1 hl⟩
        rw [hp] at h0
        exact nomatch h0

/-- **What an accepting constructor check establishes**, with the fields' sorts: the ordinary
constant check, the result shape, the parameters' pins, the opened telescope and its fields' sorts. -/
abbrev SumCtorRun (mode : CheckMode) (F : Nat) (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat)
    (cvTa cvCa : ConstantVal) (sorts : List Level) : Prop :=
  (cvCa = cvC ∧ checkConstantVal (fueledOps mode F) env cvC = .ok ()) ∧
  (∃ cbs es, cvCa.type.stripPis (nP + nF)
    = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (structPsAt nF nP ++ es)) ∧
    es.length = nIdx) ∧
  ∃ (fvsP : List Expr) (crest : Expr) (tfvs : List Expr) (trest : Expr)
    (xFvs : List Expr) (idxArgs : List Expr),
    openPisAtFvars nP cvCa.type 0 = some (fvsP, crest) ∧
    openPisAtFvars nP cvTa.type 0 = some (tfvs, trest) ∧
    checkStructDomsAt (fueledOps mode F) env 0 fvsP
      (tfvs.map Expr.fvarTypeD) nP = .ok () ∧
    openPisAtFvars nF crest nP
      = some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)) ∧
    idxArgs.length = nIdx ∧
    (∀ x ∈ xFvs, x.fvarTypeD.constsResolve env₀ = true) ∧
    (∀ e ∈ idxArgs, e.constsResolve env₀ = true) ∧
    FieldSorts mode F env isProp large resSort nP xFvs idxArgs nF sorts

/-- `checkSumCtor`, inverted. -/
theorem checkSumCtor_inv {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvC cvTa : ConstantVal}
    {nF : Nat} {F : Nat}
    (h : checkSumCtor (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok ()) :
    ∃ sorts, SumCtorRun mode F env₀ env T lps nP nIdx resSort isProp large cvC nF cvTa cvC sorts := by
  unfold checkSumCtor at h
  obtain ⟨u₀, hccv₀, h⟩ := exceptBind_ok h
  cases u₀
  dsimp only at h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cbs, cbody⟩ := q
  have hq' := unwrapOr_ok hq
  try simp only at h
  by_cases hc : structCtorResidOk T lps nP nF nIdx cbody = true
  case neg => rw [ite_eq_right hc] at h; close_throw
  rw [ite_eq_left hc] at h
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
  case neg => rw [ite_eq_right h2] at h; close_throw
  rw [ite_eq_left h2] at h
  by_cases h3 : (xFvs.all fun x => Expr.constsResolve env₀ x.fvarTypeD) = true
  case neg => rw [ite_eq_right h3] at h; close_throw
  rw [ite_eq_left h3] at h
  by_cases h4 : ((xrest.getAppArgs.drop nP).all fun e => Expr.constsResolve env₀ e) = true
  case neg => rw [ite_eq_right h4] at h; close_throw
  rw [ite_eq_left h4] at h
  obtain ⟨sorts, hsorts⟩ := checkStructFieldSortsI_inv h
  -- the two residual tests, read back as spines
  simp only [structCtorResidOk, Bool.and_eq_true, beq_iff_eq] at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨es, hes, hesl⟩ := residual_shape hc.1.1 hc.2 hc.1.2
  refine ⟨sorts, ⟨rfl, hccv₀⟩, ⟨cbs, es, by rw [hq', hes], hesl⟩,
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

/-- **What an accepting constructor loop establishes**, positionally: every entry is its constructor's
run, with its fields' sorts. -/
abbrev SumCtorsRun (mode : CheckMode) (F : Nat) (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (cvTa : ConstantVal)
    (cs ctorList : List (ConstantVal × Nat)) (sortss : List (List Level)) : Prop :=
  ctorList.length = cs.length ∧ sortss.length = cs.length ∧
  ∀ (j : Nat) (c ctor : ConstantVal × Nat), cs[j]? = some c → ctorList[j]? = some ctor →
    ctor.2 = c.2 ∧
    ∃ sorts, sortss[j]? = some sorts ∧
    SumCtorRun mode F env₀ env T lps nP nIdx resSort isProp large c.1 c.2 cvTa ctor.1 sorts

/-- All constructors, positionally. -/
theorem checkSumCtors_inv {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal} {F : Nat} :
    ∀ {cs : List (ConstantVal × Nat)},
      checkSumCtors (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large cvTa cs = .ok () →
      ∃ sortss, SumCtorsRun mode F env₀ env T lps nP nIdx resSort isProp large cvTa cs cs sortss
  | [], _ => ⟨[], rfl, rfl, fun j c ctor hc _ => by simp at hc⟩
  | c :: cs, h => by
    unfold checkSumCtors at h
    obtain ⟨u, hc, h⟩ := exceptBind_ok h
    cases u
    obtain ⟨sorts, hS⟩ := checkSumCtor_inv hc
    obtain ⟨srest, hlen, hlenS, hall⟩ := checkSumCtors_inv h
    refine ⟨sorts :: srest, rfl, by simp [hlenS], ?_⟩
    intro j c' ctor hc' hctor
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc' hctor
      subst hc'; subst hctor
      exact ⟨rfl, sorts, rfl, hS⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hc' hctor
      exact hall j c' ctor hc' hctor


/-!
## The constructors' conses: environment well-formedness

`EnvWF` across the constructors' conses (`consSumCtors`, each a checked
constant), read off the stages' own guards, and the stored rules'
membership fact (`sumRules`, never `.nested`).
-/


/-- A constructor's run at the former's environment: its type is
closed and bounded. -/
theorem direct_sum_ctor_typeWF {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvC cvTa cvCa : ConstantVal}
    {nF : Nat} {F : Nat} {sorts : List Level}
    (h : SumCtorRun mode F env₀ env T lps nP nIdx resSort isProp large cvC nF cvTa cvCa sorts) :
    cvCa.type.hasFvar = false ∧ cvCa.type.allLevelParamsDefined cvCa.levelParams = true ∧
    cvCa.type.constsResolve env = true ∧ cvCa.type.looseBVarsBounded 0 = true ∧
    LitShapeAt cvCa := by
  obtain ⟨⟨rfl, hccv⟩, -, -⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := checkConstantVal_typeWF hccv
  exact ⟨g1, g2, g3, g4, checkConstantVal_litShapeAt hccv⟩

/-- **One constructor's cons keeps well-formedness**: the stored constructor is a closed,
resolving constant, stored at the family its type concludes in. -/
theorem envWF_cons_ctor {env : Env} {cv : ConstantVal} {nP nF : Nat} {T : Name} (henv : EnvWF env)
    (h1 : cv.type.hasFvar = false) (h2 : cv.type.allLevelParamsDefined cv.levelParams = true)
    (h3 : cv.type.constsResolve env = true) (h4 : cv.type.looseBVarsBounded 0 = true)
    (hs : LitShapeAt cv) (hh : ∃ us, cv.type.piResult.getAppFn = .const T us) :
    EnvWF ⟨.ctorInfo cv nP nF T :: env.consts, env.tables⟩ :=
  EnvWF.cons (hs _ rfl) henv (structConstWF h1 h2 (Expr.constsResolve_mono h3) h4
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq))
    (hk := let ⟨_, h⟩ := hh; CtorWF.of_head h)

/-- An application spine over a head that is not a `∀` is its own `piResult`. -/
theorem piResult_mkAppN_of_ne : ∀ (args : List Expr) (f : Expr),
    (∀ b c, f ≠ .forallE b c) → (Expr.mkAppN f args).piResult = Expr.mkAppN f args
  | [], f, hf => by
    cases f with
    | forallE b c => exact absurd rfl (hf b c)
    | _ => rfl
  | a :: as, f, _ => piResult_mkAppN_of_ne as (.app f a) (fun _ _ h => nomatch h)

/-- **A syntactic telescope ending in a constant application** has that constant at the head
of its `piResult`. -/
theorem piResult_getAppFn_of_stripPis {I : Name} {us : List Level} :
    ∀ (n : Nat) {e : Expr} {bs : List Expr} {args : List Expr},
      e.stripPis n = some (bs, Expr.mkAppN (.const I us) args) →
      (e.piResult).getAppFn = .const I us
  | 0, e, bs, args, h => by
    simp only [ConLeche.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2, piResult_mkAppN_of_ne args (.const I us) (fun _ _ h => nomatch h),
      Expr.getAppFn_mkAppN]
    rfl
  | n + 1, e, bs, args, h => by
    match e with
    | .forallE ty b =>
      simp only [ConLeche.Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', r⟩, hr, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      show b.piResult.getAppFn = _
      exact piResult_getAppFn_of_stripPis n hr
    | .bvar _ | .sort _ | .const _ _ | .lit _ | .fvar _ _ | .app _ _ | .lam _ _
    | .letE _ _ _ | .proj _ _ _ => exact absurd h (by simp [ConLeche.Expr.stripPis])

/-- **A checked constructor's declared type concludes in the family it is checked against**
(`checkSumCtor`'s result shape): the fact its stored `induct` carries (`CtorWF`). -/
theorem SumCtorRun.head {env₀ env₁ : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvC cvTa cvCa : ConstantVal}
    {nF : Nat} {F : Nat} {sorts : List Level}
    (h : SumCtorRun mode F env₀ env₁ T lps nP nIdx resSort isProp large cvC nF cvTa cvCa sorts) :
    ∃ us, cvCa.type.piResult.getAppFn = .const T us := by
  obtain ⟨-, ⟨cbs, es, hst, -⟩, -⟩ := h
  exact ⟨_, piResult_getAppFn_of_stripPis _ hst⟩

/-- **A checked constructor's cons keeps well-formedness**, at any well-formed environment its
type resolves at (the constructor stage's step). -/
theorem SumCtorRun.envWF_cons {env₀ env₁ : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvC cvTa cvCa : ConstantVal}
    {nF : Nat} {F : Nat} {sorts : List Level}
    (h : SumCtorRun mode F env₀ env₁ T lps nP nIdx resSort isProp large cvC nF cvTa cvCa sorts)
    {env : Env} (henv : EnvWF env) (hres : cvCa.type.constsResolve env = true) :
    EnvWF ⟨.ctorInfo cvCa nP nF T :: env.consts, env.tables⟩ := by
  obtain ⟨g1, g2, -, g4, g5⟩ := direct_sum_ctor_typeWF h
  exact envWF_cons_ctor henv g1 g2 hres g4 g5 h.head

/-- A name fresh above the constructors' conses is fresh below them
(#210). -/
theorem consSumCtors_find?_none {nP : Nat} {T : Name} {n : Name} :
    ∀ {ctorList : List (ConstantVal × Nat)} {env : Env},
      (consSumCtors nP T ctorList env).find? n = none → env.find? n = none
  | [], _, h => h
  | c :: cs, env, h => by
    simp only [consSumCtors] at h
    have h' := consSumCtors_find?_none h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- The constructors' conses keep well-formedness: every consed
constructor's type resolves at the environment it is consed onto
(resolution is monotone along the conses). -/
theorem envWF_consSumCtors {nP : Nat} {T : Name} :
    ∀ {ctorList : List (ConstantVal × Nat)} {env : Env},
      EnvWF env →
      (∀ c ∈ ctorList, c.1.type.hasFvar = false ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true ∧ LitShapeAt c.1 ∧
        ∃ us, c.1.type.piResult.getAppFn = .const T us) →
      EnvWF (consSumCtors nP T ctorList env)
  | [], _, henv, _ => henv
  | c :: cs, env, henv, hall => by
    simp only [consSumCtors]
    obtain ⟨htf, htp, htr, htb, hts, hth⟩ := hall c List.mem_cons_self
    refine envWF_consSumCtors ?_ ?_
    · exact envWF_cons_ctor henv htf htp htr htb hts hth
    · intro c' hc'
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hall c' (List.mem_cons_of_mem _ hc')
      exact ⟨h1, h2, Expr.constsResolve_mono h3, h4, h5, h6⟩

/-- The stored rules carry the generated right-hand sides and are
never `.nested`. -/
theorem sumRules_mem :
    ∀ {ctorList : List (ConstantVal × Nat)} {rhss : List Expr} {r : RecRule},
      r ∈ sumRules ctorList rhss →
      r.rhs ∈ rhss ∧ ∀ lvls pins, r.fire ≠ .nested lvls pins
  | [], _, r, h => by simp [sumRules] at h
  | _ :: _, [], r, h => by simp [sumRules] at h
  | c :: cs, rhs :: rhss, r, h => by
    simp only [sumRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨List.mem_cons_self, fun lvls pins h => nomatch h⟩
    · obtain ⟨hm, hf⟩ := sumRules_mem h
      exact ⟨List.mem_cons_of_mem _ hm, hf⟩

end ConLeche
