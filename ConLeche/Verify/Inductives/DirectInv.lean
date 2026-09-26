module

public import ConLeche.Verify.BridgeWfImp
public import ConLeche.Verify.ExceptBind
import ConLeche.Verify.FastOps
import ConLeche.Kernel.Inductives.SumInstall

public section

/-!
# The single-constructor and constructor-list stage runs, inverted

Environment well-formedness of the direct installs, their stage runs
inverted to their records, the recogniser and the projection slots
inverted, and the constructor-list (sum) versions.
-/

/-!
## The direct simple-structure install: environment well-formedness

`EnvWF` for the environments `checkStruct` walks through — one
per installed constant — at the pure fueled run.  The consumer is the
cached driver's run bridge (`ConLeche/Verify/Cached/BridgeCSDecl.lean`,
`checkStructS_run`), which threads the well-formedness of every
intermediate environment through the per-stage simulations.

Every fact is read off the stage's own guards: each install stores an
annotated constant whose type (and, for the recursor, whose rule's
right-hand side; for a projection entry, whose stored type) was
checked closed, level-defined, resolving and bound *by the stage
itself*, so the inversions here are shape walks (`exceptBind_ok` /
`split`) that keep exactly those guards.
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
`thmInfo` clause defaulted, as every constant installed by the direct
path is an inductive-kind one). -/
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
    (h6 : ∀ cv mI rP rules, c = .recInfo cv mI rP rules →
      ∀ r, r ∈ rules →
        (RecRule.rhs r).hasFvar = false ∧
        (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
        (RecRule.rhs r).constsResolve env = true ∧
        (RecRule.rhs r).looseBVarsBounded 0 = true ∧
        ∀ lvls pins, RecRule.fire r = .nested lvls pins →
          rP ≤ mI ∧
          (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
          (∀ pin ∈ pins, pin.hasFvar = false ∧
            pin.allLevelParamsDefined cv.levelParams = true ∧
            pin.constsResolve env = true ∧
            pin.looseBVarsBounded rP = true) ∧
          ∃ pre dom body bm D,
            cv.type.stripPis mI = some (pre, .forallE dom body bm) ∧
            dom.getAppFn = .const D lvls ∧
            dom.getAppArgs =
              pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
                (List.range (mI - rP)).map
                  (fun i => Expr.bvar (mI - rP - 1 - i)))
    (h8 : ∀ tbl, c = .projInfo tbl →
      tbl.bodies.size = tbl.numFields ∧
      ∀ (i : Nat) (b : Expr), tbl.bodies[i]? = some b →
        b.hasFvar = false ∧
        b.allLevelParamsDefined tbl.levelParams = true ∧
        b.constsResolve env = true ∧
        b.looseBVarsBounded (tbl.numParams + 1) = true := by
        intro tbl h
        exact ConstantInfo.noConfusion h)
    (h9 : IndCapsWF c := by
        intro cv caps h
        exact ConstantInfo.noConfusion h) :
    ConstWF env c := ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩

/-! ## Stage 5: the projection table (task #175 S1) -/

/-- The table stage's run, inverted: the bodies are the generator's,
they pass the scoping guard, the table name is fresh, and the output
is the table consed. -/
theorem checkStructProjTable_inv {env envOut : Env} {T C : Name}
    {lps : List Name} {nP nF : Nat} {rs : Level} {guards : List Level}
    {cvCa : ConstantVal}
    (h : checkStructProjTable (m := CheckM) T C lps nP nF rs guards off cvCa env
      = .ok envOut) :
    ∃ bodies : Array Expr,
      structProjBodies T nP nF cvCa.type = some bodies ∧
      (bodies.size = nF ∧ bodies.all (fun b => !b.hasFvar &&
        b.allLevelParamsDefined lps && b.constsResolve env &&
        b.looseBVarsBounded (nP + 1)) = true) ∧
      (List.range nF).all (fun j => (env.find? (projFnName T j)).isNone) = true ∧
      env.find? (projTableName T) = none ∧
      envOut = ⟨.projInfo ⟨T, lps, nP, C, nF, rs, bodies, guards, off⟩
        :: env.consts⟩ := by
  unfold checkStructProjTable at h
  obtain ⟨bodies, hb, h⟩ := exceptBind_ok h
  have hb' := unwrapOr_ok hb
  repeat' first
    | (obtain ⟨_, _, h⟩ := exceptBind_ok h)
    | split at h
  all_goals first
    | (try dsimp only at h
       simp only [pure, Except.pure, Except.ok.injEq] at h
       refine ⟨bodies, hb', by assumption, by assumption,
         Option.isNone_iff_eq_none.mp (by assumption), h.symm⟩)
    | close_throw

/-- The projection-table stage at the run level (task #175 S1): the
environment it produces is well-formed — the table's constant type is
the closed `Sort 1`, and the bodies' scoping is the stage's own guard. -/
theorem direct_table_wf {env envOut : Env} (henv : EnvWF env)
    {T C : Name} {lps : List Name} {nP nF : Nat} {rs : Level}
    {guards : List Level} {off : Nat} {cvCa : ConstantVal}
    (h : checkStructProjTable (m := CheckM) T C lps nP nF rs guards off cvCa env
      = .ok envOut) :
    EnvWF envOut := by
  obtain ⟨bodies, -, ⟨hsize, hall⟩, -, -, rfl⟩ := checkStructProjTable_inv h
  refine EnvWF.cons henv (structConstWF rfl rfl rfl rfl
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq) ?_)
  intro tbl heq
  obtain rfl := ConstantInfo.projInfo.inj heq
  refine ⟨hsize, fun i b hb => ?_⟩
  have hmem : b ∈ bodies := Array.mem_of_getElem? hb
  have hb' := (Array.all_eq_true_iff_forall_mem.mp hall) b hmem
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hb'
  exact ⟨hb'.1.1.1, hb'.1.1.2, Expr.constsResolve_mono hb'.1.2, hb'.2⟩


/-!
## The direct install's stage runs, inverted to their records

Each stage of `checkStruct` is a `do`-block of guards and
operation runs; the P install reads those runs (the annotated types'
inference, the definitional pins at the opened frames, the field
sorts) as its premises.  This module inverts every stage into exactly
the facts the semantic modules consume — named runs, at the frames
the checker ran them.  Shape walks only: `exceptBind_ok` per bind,
`rw [if_pos …]` per guard (BridgeWfImp's idiom — the do-notation's
join points defeat a bare `split`), `close_throw` on the failing
branches.
-/


/-! ## The frame walks: binder-domain pins and field sorts -/

/-- `checkStructDomsAt`, inverted: every position below the walk's
bound carries a successful `isDefEqCore` at its own frame. -/
theorem checkStructDomsAt_inv {env : Env} {F off : Nat} {fvs doms : List Expr} :
    ∀ {j : Nat},
      checkStructDomsAt (fueledOps mode F) env off fvs doms j = .ok () →
      ∀ i, i < j → ∃ a b, fvs[i]? = some a ∧ doms[i]? = some b ∧
        isDefEqCore mode env F (off + i) (Expr.fvarTypeD a) b = .ok true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | j + 1, h, i, hi => by
    unfold checkStructDomsAt at h
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
    · exact checkStructDomsAt_inv h i hij
    · obtain rfl : i = j := by omega
      exact ⟨a, b, ha', hb', hc'⟩


/-!
## The direct recogniser and the projection slots, inverted

V-free facts the direct install's assembly reads off the kernel's
recogniser and slot decision:

* `structParts?_inv`: the block's shape facts the recogniser pins —
  the propositionality datum is the result sort's, the recursor is
  `T.rec` at the block's level parameters (plus the large eliminator's
  fresh one), the constructor carries the former's;
* `structProjGuards_getD`: the coarse guard's spelling at a slot.
  (Task #175 S1: the per-slot run and the slot-prefix lemmas went with
  the per-field entries — the table stage is one cons,
  `checkStructProjTable_inv`.)
-/


/-! ## The guard's spelling -/

theorem structProjGuards_getD (cty : Expr) (nP nF : Nat) (sorts : List Level) {i : Nat}
    (hi : i < nF) :
    (structProjGuards cty nP nF sorts).getD i .zero
      = (List.range i).foldl
          (fun acc j => if structUsedLater cty nP j then Level.max acc (sorts.getD j .zero)
            else acc)
          (sorts.getD i .zero) := by
  unfold structProjGuards
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl


/-!
## The direct sum install's stage runs, inverted

Each stage of `checkSum` inverted to the facts the semantic
modules consume: the type former's run, every constructor's run at the
former's environment (`checkSumCtors_inv`, positionally), the
generated recursor's comparison and every generated rule's run
(`checkSumRules_inv`), and the recogniser's pins
(`sumParts?_inv`).  Shape walks only, as `DirectInv.lean`.

Task #175 indexed: every stage carries the index count `nIdx`, the
constructor's residual is the family at the parameters followed by
`nIdx` index expressions (`structCtorResidOk`, inverted by
`residual_shape` below), and the field-sort walk is
`checkStructFieldSortsI` (inverted by `checkStructFieldSortsI_inv`,
whose large-eliminator clause admits a non-propositional field that is
one of the index expressions).
-/


/-! ## The residual test, inverted (task #175 indexed) -/

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

/-- `checkSumTele`, inverted (task #195): either the declared
type was the telescope (the checked constant is the input, its type
strips to the sort), or the whnf'd telescope was checked from scratch
as the former's type at the block's name and level parameters — the
run of `checkConstantVal` is all the later stages consume, whichever
branch produced it. -/
theorem checkSumTele_shape {env : Env} {cv : ConstantVal} {n : Nat}
    {cvTa₀ cvTa : ConstantVal} {s : Level} {F : Nat}
    (h : checkSumTele (fueledOps mode F) env cv n cvTa₀ = .ok (cvTa, s)) :
    (cvTa = cvTa₀ ∧ ∃ bs, cvTa₀.type.stripPis n = some (bs, .sort s)) ∨
    ∃ ty, checkConstantVal (fueledOps mode F) env { cv with type := ty } = .ok cvTa := by
  unfold checkSumTele at h
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

/-! ## Stage 2: one constructor -/

/-- `checkStructFieldSortsI`, inverted (task #175 indexed): the sorts
are returned in field order, one per field, each the `ensureSort` of
the field annotation's inferred type at the field's own frame, under
the official universe bound (`isProp = false`) or — at a large
eliminator on a `Prop` family — the subsingleton-elimination criterion:
the field is a proposition OR one of the residual's index expressions
(`checkStructFieldSorts_inv` widened). -/
theorem checkStructFieldSortsI_inv {env : Env} {isProp large : Bool}
    {s : Level} {nP F : Nat} {fvs idxArgs : List Expr} :
    ∀ {j : Nat} {sorts : List Level},
      checkStructFieldSortsI (fueledOps mode F) env isProp large s nP fvs idxArgs j
        = .ok sorts →
      sorts.length = j ∧
      ∀ i, i < j → ∃ fv ty u, fvs[i]? = some fv ∧ sorts[i]? = some u ∧
        inferTypeCore mode env F (nP + i) (Expr.fvarTypeD fv) = .ok ty ∧
        ensureSortCore mode env F (nP + i) ty = .ok u ∧
        (isProp = false → Level.leq u s = some true) ∧
        (isProp = true → large = true →
          (Level.isEquiv u .zero == some true) = true ∨ idxArgs.contains fv = true)
  | 0, sorts, h => by
    simp only [checkStructFieldSortsI, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | j + 1, sorts, h => by
    unfold checkStructFieldSortsI at h
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
        checkStructFieldSortsI (fueledOps mode F) env isProp large s nP fvs idxArgs j
          = .ok rest ∧ sorts = rest ++ [u] ∧
        (isProp = false → Level.leq u s = some true) ∧
        (isProp = true → large = true →
          (Level.isEquiv u .zero == some true) = true ∨ idxArgs.contains fv = true) by
      obtain ⟨rest, hrest, rfl, hleq, hz⟩ := hs
      obtain ⟨hlen, hall⟩ := checkStructFieldSortsI_inv hrest
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

theorem checkSumCtor_shape {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvC cvTa cvCa : ConstantVal}
    {nF : Nat} {F : Nat} {sorts : List Level}
    (h : checkSumCtor (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok (cvCa, sorts)) :
    (∃ ty', checkConstantVal (fueledOps mode F) env { cvC with type := ty' } = .ok cvCa) ∧
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
      checkStructFieldSortsI (fueledOps mode F) env isProp large resSort
        nP xFvs idxArgs nF = .ok sorts := by
  unfold checkSumCtor at h
  obtain ⟨cvCa', hccv₀, h⟩ := exceptBind_ok h
  have hccv : ∃ ty', checkConstantVal (fueledOps mode F) env { cvC with type := ty' }
      = .ok cvCa' := ⟨cvC.type, hccv₀⟩
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
the input and every entry is its constructor's run. -/
theorem checkSumCtors_inv {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal} {F : Nat} :
    ∀ {cs ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)},
      checkSumCtors (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
        cvTa cs = .ok (ctorsA, sortss) →
      ctorsA.length = cs.length ∧ sortss.length = cs.length ∧
      ∀ (j : Nat) (c cA : ConstantVal × Nat), cs[j]? = some c → ctorsA[j]? = some cA →
        cA.2 = c.2 ∧
        ∃ sorts, sortss[j]? = some sorts ∧
        checkSumCtor (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
          c.1 c.2 cvTa = .ok (cA.1, sorts)
  | [], ctorsA, sortss, h => by
    simp only [checkSumCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, fun j c cA hc _ => by simp at hc⟩
  | c :: cs, ctorsA, sortss, h => by
    unfold checkSumCtors at h
    obtain ⟨q, hc, h⟩ := exceptBind_ok h
    obtain ⟨cvCa, sorts⟩ := q
    try simp only at h
    obtain ⟨q', hrest, h⟩ := exceptBind_ok h
    obtain ⟨rest, srest⟩ := q'
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hlen, hlenS, hall⟩ := checkSumCtors_inv hrest
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


/-!
## The direct sum install: environment well-formedness

`EnvWF` for the environments `checkSum` walks through, read off
the stages' own guards (as `DirectInv.lean` for the structure route):
the former's cons, the constructors' conses (`consSumCtors`, each a
checked constant), the recursor's cons with its rules (each rule's
right-hand side scoped by `checkSumRules`, never `.nested`).
Task #175 indexed: the recursor's cons is generic over its major index
and rule prefix (`p.majorIdx`/`p.rulePrefix` at the install).
-/


/-- A constructor's run at the former's environment: its type is
closed and bounded. -/
theorem direct_sum_ctor_typeWF {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvC cvTa cvCa : ConstantVal}
    {nF : Nat} {F : Nat} {sorts : List Level}
    (h : checkSumCtor (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok (cvCa, sorts)) :
    cvCa.type.hasFvar = false ∧ cvCa.type.allLevelParamsDefined cvCa.levelParams = true ∧
    cvCa.type.constsResolve env = true ∧ cvCa.type.looseBVarsBounded 0 = true := by
  obtain ⟨⟨_, hccv⟩, -, -⟩ := checkSumCtor_shape h
  exact checkConstantVal_typeWF hccv

/-- A name fresh above the constructors' conses is fresh below them
(task #210 Part A). -/
theorem consSumCtors_find?_none {nP : Nat} {n : Name} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      (consSumCtors nP ctorsA env).find? n = none → env.find? n = none
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
theorem envWF_consSumCtors {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      EnvWF env →
      (∀ c ∈ ctorsA, c.1.type.hasFvar = false ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true) →
      EnvWF (consSumCtors nP ctorsA env)
  | [], _, henv, _ => henv
  | c :: cs, env, henv, hall => by
    simp only [consSumCtors]
    obtain ⟨htf, htp, htr, htb⟩ := hall c List.mem_cons_self
    refine envWF_consSumCtors ?_ ?_
    · exact EnvWF.cons henv (structConstWF htf htp (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
    · intro c' hc'
      obtain ⟨h1, h2, h3, h4⟩ := hall c' (List.mem_cons_of_mem _ hc')
      exact ⟨h1, h2, Expr.constsResolve_mono h3, h4⟩

/-- The stored rules carry the generated right-hand sides and are
never `.nested`. -/
theorem sumRules_mem {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {r : RecRule},
      r ∈ sumRules find? recName nP mI rP recTy ctorsA rhss →
      r.rhs ∈ rhss ∧ ∀ lvls pins, r.fire ≠ .nested lvls pins
  | [], _, r, h => by simp [sumRules] at h
  | _ :: _, [], r, h => by simp [sumRules] at h
  | c :: cs, rhs :: rhss, r, h => by
    simp only [sumRules, List.mem_cons] at h
    rcases h with rfl | h
    · refine ⟨List.mem_cons_self, fun lvls pins => ?_⟩
      show (if Expr.recRulePlain recTy mI rP nP then RecRuleFire.plain else .inert) ≠ _
      split <;> simp
    · obtain ⟨hm, hf⟩ := sumRules_mem h
      exact ⟨List.mem_cons_of_mem _ hm, hf⟩

end ConLeche
