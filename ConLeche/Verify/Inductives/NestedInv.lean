module

public import ConLeche.Verify.Inductives.MutualInv
public import ConLeche.Kernel.Inductives.NestedInstall
import ConLeche.Verify.Inductives.FrontDoor
public import ConLeche.Semantics.ConstsBound

public section

/-!
# The nested install: inversion (task #279)

The shape of a successful run of `checkNested`
(`ConLeche/Kernel/Inductives/NestedInstall.lean`), read off the monad
exactly as `MutualInv.lean` reads the mutual install's: the two
syntactic front guards, the pure elimination and its mimic count, the
auxiliary block, the mutual install in the scratch environment, the
read-back, the restored constructors, recursor types and rules, the
projection tables, and the two post-checks — closing with the chain of
`∃`s that `ConLeche/Semantics/Inductives/DeclNested.lean` records as a
run and the model tier consumes.

Shape walks only: `exceptBind_ok` per bind, `rw [if_pos …]` per guard,
`close_throw` on the failing branches.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A thrown step never succeeds. -/
private theorem nestThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact nestThrow_ne_ok (by assumption))
        | (exfalso; exact nestThrow_ne_ok h)
        | (simp at h))

/-- `nestedLift` succeeds only on an `.ok`. -/
theorem nestedLift_ok {α : Type} {r : Except CheckError α} {a : α}
    (h : (nestedLift (m := CheckM) r) = .ok a) : r = .ok a := by
  unfold nestedLift at h
  cases r with
  | ok b => cases h; rfl
  | error e => exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

/-- `Except.mapError` does not move an `.ok`. -/
theorem mapError_ok {α ε ε' : Type} {f : ε → ε'} {x : Except ε α} {a : α}
    (h : x.mapError f = .ok a) : x = .ok a := by
  cases x with
  | ok b => cases h; rfl
  | error e => exact absurd h (by simp [Except.mapError])

/-! ## The copies' stored types ARE the re-minted ones (task #279 K.10)

`checkConstantValPre` returns its input and `checkSumTele` returns a
telescope that already ends in a sort unchanged; at `auxRoute` a
`_nested`-named member goes through both, so the formers stage stores
exactly the type the elimination minted.  Nothing about the annotation
pass is used — this is a chain of two definitional facts, and it is what
the model tier reads instead of an `AnnotStable` hypothesis. -/

/-- **The pre-annotated front door, inverted** — it returns its input,
and it has VALIDATED the `.proj` nodes of that input (K.13: the
structure-name slot, which on the annotated path the walk checks). -/
theorem checkConstantValPre_inv {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvA) :
    cvA = cv ∧ cv.type.projTablesOk env = true := by
  unfold checkConstantValPre at h
  by_cases h1 : (env.find? cv.name).isSome = true
  case pos => rw [if_pos h1] at h; close_throw
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  case pos => rw [if_pos h2] at h; close_throw
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  case pos => rw [if_pos h3] at h; close_throw
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; close_throw
  rw [if_pos h4] at h
  by_cases h5 : cv.type.looseBVarsBounded 0 = true
  case neg => rw [if_neg h5] at h; close_throw
  rw [if_pos h5] at h
  by_cases h6 : cv.type.hasFvar = true
  case pos => rw [if_pos h6] at h; close_throw
  rw [if_neg h6] at h
  by_cases h7 : cv.type.allLevelParamsDefined cv.levelParams = true
  case neg => rw [if_neg h7] at h; close_throw
  rw [if_pos h7] at h
  by_cases h8 : cv.type.constsResolve env = true
  case neg => rw [if_neg h8] at h; close_throw
  rw [if_pos h8] at h
  by_cases h9 : cv.type.projTablesOk env = true
  case neg => rw [if_neg h9] at h; close_throw
  rw [if_pos h9] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨_sty, _hinf, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨_u, _hens, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨h.symm, h9⟩

/-- The pre-annotated front door returns its input: every check of
`checkConstantVal` runs, and the stored type is the input type. -/
theorem checkConstantValPre_ok {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvA) :
    cvA = cv := (checkConstantValPre_inv h).1

/-- **THE PRE-ANNOTATED FRONT DOOR'S `typeWF`** (task #279 K.20): the
four type-slot facts `EnvWF` asks of every stored constant, off the
no-walk front door.  They are its own guards — the walk contributed
none of them; `checkConstantVal_typeWF` has to work for them because its
type is the ANNOTATED one, and here the stored type IS the input. -/
theorem checkConstantValPre_typeWF {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvA) :
    cvA.type.hasFvar = false ∧
    cvA.type.allLevelParamsDefined cvA.levelParams = true ∧
    cvA.type.constsResolve env = true ∧
    cvA.type.looseBVarsBounded 0 = true := by
  rw [checkConstantValPre_ok h]
  unfold checkConstantValPre at h
  by_cases h1 : (env.find? cv.name).isSome = true
  case pos => rw [if_pos h1] at h; close_throw
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  case pos => rw [if_pos h2] at h; close_throw
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  case pos => rw [if_pos h3] at h; close_throw
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; close_throw
  rw [if_pos h4] at h
  by_cases h5 : cv.type.looseBVarsBounded 0 = true
  case neg => rw [if_neg h5] at h; close_throw
  rw [if_pos h5] at h
  by_cases h6 : cv.type.hasFvar = true
  case pos => rw [if_pos h6] at h; close_throw
  rw [if_neg h6] at h
  by_cases h7 : cv.type.allLevelParamsDefined cv.levelParams = true
  case neg => rw [if_neg h7] at h; close_throw
  rw [if_pos h7] at h
  by_cases h8 : cv.type.constsResolve env = true
  case neg => rw [if_neg h8] at h; close_throw
  exact ⟨Bool.not_eq_true _ |>.mp h6, h7, h8, h5⟩

/-- **THE `.proj` FACT THE MODEL TIER READS** (K.13).  On the
pre-annotated path there is no annotation walk to validate a `.proj`
node's structure-name slot, so `checkConstantValPre` asks the same
condition itself: every `.proj sn i e` in the checked type has a
projection-table entry AT ITS OWN NAME and index.  Whenever the walk
accepted such a node it had `findProj? T i = some entry` with `T = sn`,
so this narrows nothing — and it is what discharges the model lane's
`CtorsNoProj`-style hypothesis at grade `true`. -/
theorem checkConstantValPre_projOk {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvA) :
    cv.type.projTablesOk env = true := (checkConstantValPre_inv h).2

/-- `checkSumTele` is the identity on a type whose telescope already
ends in a sort (task #218's syntactic-telescope arm). -/
theorem checkSumTele_id {env : Env} {cv cvTa₀ cvTa : ConstantVal} {n F : Nat}
    {s s' : Level} {bs : List (Expr × BinderMeta)}
    (hstrip : cvTa₀.type.stripPis n = some (bs, Expr.sort s'))
    (h : checkSumTele (m := CheckM) (fueledOps mode F) env cv n cvTa₀ = .ok (cvTa, s)) :
    cvTa = cvTa₀ := by
  unfold checkSumTele at h
  rw [hstrip] at h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact h.1.symm

/-- The formers stage at `auxRoute`, one member: the front door is
`checkConstantValPre` (K.12 — the grade is the block's, no name is
read), and the stored former is the one `checkSumTele` returned. -/
theorem mutualFormerChecks_true_cons {nP F : Nat} {cv : ConstantVal} {nIdx : Nat}
    {rest : List (ConstantVal × Nat)} {env : Env} {fms : List MutualFormerA}
    (h : mutualFormerChecks (fueledOps mode F) env nP true ((cv, nIdx) :: rest) = .ok fms) :
    ∃ (cvTa₀ cvTa : ConstantVal) (s : Level) (fs : List MutualFormerA),
      checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvTa₀ ∧
      checkSumTele (fueledOps mode F) env cv (nP + nIdx) cvTa₀ = .ok (cvTa, s) ∧
      mutualFormerChecks (fueledOps mode F) env nP true rest = .ok fs ∧
      fms = ⟨cvTa, nIdx, s⟩ :: fs := by
  unfold mutualFormerChecks at h
  simp only [if_true] at h
  obtain ⟨cvTa₀, hccv, h⟩ := exceptBind_ok h
  obtain ⟨q, htele, h⟩ := exceptBind_ok h
  obtain ⟨cvTa, s⟩ := q
  try simp only at h
  obtain ⟨q2, _hq2, h⟩ := exceptBind_ok h
  obtain ⟨_bs, tbody⟩ := q2
  try simp only at h
  by_cases hc : (tbody == Expr.sort s) = true
  case neg => rw [if_neg hc] at h; close_throw
  rw [if_pos hc] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨fs, hrec, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨cvTa₀, cvTa, s, fs, hccv, htele, hrec, h.symm⟩

/-- **THE MEMBERS' TYPES, READY-MADE** (K.10, widened by K.12).  At
`auxRoute` EVERY member of the block is stored WITH THE TYPE IT WAS
GIVEN, provided that type already strips its telescope to a sort —
which is exactly what `auxIdxCount` read off it when `auxBlock` recorded
the member's index count.  No annotation-stability hypothesis anywhere:
the walk does not run on this block at all. -/
theorem mutualFormerChecks_true_id {nP F : Nat} {env : Env} :
    ∀ {formers : List (ConstantVal × Nat)} {fms : List MutualFormerA},
      mutualFormerChecks (fueledOps mode F) env nP true formers = .ok fms →
      ∀ (i : Nat) (cv : ConstantVal) (nIdx : Nat),
        formers[i]? = some (cv, nIdx) →
        (∃ (bs : List (Expr × BinderMeta)) (s : Level),
          cv.type.stripPis (nP + nIdx) = some (bs, Expr.sort s)) →
        ∃ f : MutualFormerA, fms[i]? = some f ∧ f.cvTa.type = cv.type := by
  intro formers
  induction formers with
  | nil =>
    intro fms _h i cv nIdx hi _
    exact absurd hi (by simp)
  | cons hd rest ih =>
    intro fms h i cv nIdx hi hstrip
    obtain ⟨cv₀, nIdx₀⟩ := hd
    obtain ⟨cvTa₀, cvTa, s, fs, hfront, htele, hrec, rfl⟩ :=
      mutualFormerChecks_true_cons h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      have e1 := checkConstantValPre_ok hfront
      obtain ⟨bs', s', hs'⟩ := hstrip
      rw [← e1] at hs'
      have e2 := checkSumTele_id hs' htele
      exact ⟨_, rfl, by rw [e2, e1]⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨f, hf, hft⟩ := ih hrec k cv nIdx hi hstrip
      exact ⟨f, by simpa using hf, hft⟩

/-! ### The constructors' stage at the grade -/

/-- What the constructors' normalisation STORES at the grade: the
constant it was given, or that constant with its type replaced by the
positivity normalisation — never an annotation (K.12). -/
theorem normCtorValM_true_stores {env : Env} {memberNames : List Name} {nP nF F : Nat}
    {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa') :
    (cvCa' = cvCa ∨ ∃ ty', cvCa' = { cvC with type := ty' }) ∧
      (cvCa.type.projTablesOk env = true → cvCa'.type.projTablesOk env = true) := by
  unfold normCtorValM at h
  obtain ⟨_q, _h1, h⟩ := exceptBind_ok h
  obtain ⟨_cbs, _⟩ := _q
  try simp only at h
  obtain ⟨_r, _h2, h⟩ := exceptBind_ok h
  obtain ⟨_fvsP, _crest⟩ := _r
  try simp only at h
  obtain ⟨_u, _h3, h⟩ := exceptBind_ok h
  obtain ⟨_fbs, _resid⟩ := _u
  try simp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨Or.inl h.symm, by rw [← h]; exact id⟩
  · simp only [if_true] at h
    refine ⟨Or.inr ⟨_, checkConstantValPre_ok h⟩, fun _ => ?_⟩
    -- the re-checked constant went through the same front door, which
    -- validates the `.proj` nodes of the type it is given (K.13)
    have hp := checkConstantValPre_projOk h
    rw [checkConstantValPre_ok h]
    simpa using hp

/-- **THE STORED CONSTRUCTOR'S RESIDUAL IS THE MINTED ONE'S** (task
#315 L-B): whatever `normCtorValM` stores, its type is either the
constant it was given or that constant's telescope re-closed around
**the very residual the two-stage opening of the given type hands
back**.  Only the field domains differ. -/
theorem normCtorValM_resid {env : Env} {memberNames : List Name} {nP nF F : Nat}
    {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa') :
    cvCa' = cvCa ∨
      ∃ (pbs fbs : List (Expr × BinderMeta)) (fvs xFvs : List Expr) (crest xrest : Expr),
        openPisAtFvars nP cvCa.type 0 = some (fvs, crest) ∧
        openPisAtFvars nF crest nP = some (xFvs, xrest) ∧
        fbs.length = nF ∧
        cvCa'.type = closeTelescope (pbs ++ fbs) 0 xrest := by
  unfold normCtorValM at h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cbs, cres⟩ := q
  try simp only at h
  obtain ⟨rr, hr, h⟩ := exceptBind_ok h
  obtain ⟨fvs, crest'⟩ := rr
  try simp only at h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  obtain ⟨fbs, resid⟩ := u
  try simp only at h
  obtain ⟨xFvs, hopX, hfbs⟩ := normFieldDomsM_open hu
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  · refine Or.inr ⟨List.zipWith (fun (x : Expr) (bb : Expr × BinderMeta) => (x.fvarTypeD, bb.2))
        fvs cbs, fbs, fvs, xFvs, crest', resid, unwrapOr_ok hr, hopX, hfbs, ?_⟩
    rw [checkConstantValPre_ok h]

/-- One constructor at the grade: the front door is
`checkConstantValPre`, which returns its input, so what the stage
stores is `normCtorValM`'s output ON THE MINTED CONSTANT — the
positivity normalisation and nothing else (K.12). -/
theorem checkMutualCtor_true_norm {env : Env} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nIdx nF F : Nat} {resSort : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal} {sorts : List Level}
    (h : checkMutualCtor (fueledOps mode F) env memberNames T lps nP nIdx resSort isProp large
      cvC nF cvTa true = .ok (cvCa, sorts)) :
    normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvC true
      = .ok cvCa ∧ cvC.type.projTablesOk env = true ∧
    cvC.type.looseBVarsBounded 0 = true := by
  unfold checkMutualCtor at h
  simp only [if_true] at h
  obtain ⟨cvCa₀, hfront, h⟩ := exceptBind_ok h
  obtain ⟨c, hnorm, h⟩ := exceptBind_ok h
  have hproj := checkConstantValPre_projOk hfront
  have hbnd : cvC.type.looseBVarsBounded 0 = true := by
    have := (checkConstantValPre_typeWF hfront).2.2.2
    rwa [checkConstantValPre_ok hfront] at this
  rw [checkConstantValPre_ok hfront] at hnorm
  obtain ⟨q, _hq, h⟩ := exceptBind_ok h
  obtain ⟨_cbs, cbody⟩ := q
  try simp only at h
  by_cases hc : structCtorResidOk T lps nP nF nIdx cbody = true
  case neg => rw [if_neg hc] at h; close_throw
  rw [if_pos hc] at h
  obtain ⟨cq, _hcq, h⟩ := exceptBind_ok h
  obtain ⟨fvsP, _crest⟩ := cq
  obtain ⟨tq, _htq, h⟩ := exceptBind_ok h
  obtain ⟨_tfvs, _trest⟩ := tq
  try simp only at h
  obtain ⟨u, _hdoms, h⟩ := exceptBind_ok h
  obtain ⟨xq, _hxq, h⟩ := exceptBind_ok h
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
  obtain ⟨_sorts', _hsorts, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨hnorm, hproj, hbnd⟩

/-! ### From the auxiliary block to the copy's stored former -/

/-- A successful `mapM` in `Option`, positionally. -/
theorem mapM_option_inv {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r →
      ∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, r[i]? = some b ∧ f a = some b
  | [], _r, _h, _i, _a, hi => absurd hi (by simp)
  | a₀ :: l, r, h, i, a, hi => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨b₀, hb₀, bs, hbs, rfl⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      obtain rfl := hi
      exact ⟨b₀, rfl, hb₀⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨b, hb, hfb⟩ := mapM_option_inv hbs k a hi
      exact ⟨b, by simpa using hb, hfb⟩

/-- A syntactic telescope ending in a sort IS the greedy `∀`-walk
(task #315 M8): the converse the walk's index-count bridge needs. -/
theorem piBinders_of_stripPis_sort :
    ∀ {n : Nat} {e : Expr} {bs : List (Expr × BinderMeta)} {u : Level},
      e.stripPis n = some (bs, Expr.sort u) → e.piBinders = (bs, Expr.sort u)
  | 0, e, bs, u, h => by
      simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | n + 1, e, bs, u, h => by
      cases e with
      | forallE ty body mb =>
        simp only [Expr.stripPis, Option.map_eq_some_iff] at h
        obtain ⟨⟨bs', r⟩, hr, hbs⟩ := h
        simp only [Prod.mk.injEq] at hbs
        obtain ⟨rfl, rfl⟩ := hbs
        simp only [Expr.piBinders, piBinders_of_stripPis_sort hr]
      | _ => exact nomatch h

/-- The greedy `∀`-walk, read back as a `stripPis`: a `piBinders` ending
in a sort is a syntactic telescope of its own length (the converse of
`piBinders_of_stripPis_sort`). -/
theorem stripPis_of_piBinders_sort :
    ∀ {e : Expr} {bs : List (Expr × BinderMeta)} {u : Level},
      e.piBinders = (bs, Expr.sort u) → e.stripPis bs.length = some (bs, Expr.sort u)
  | .forallE ty body mb, bs, u, h => by
    simp only [Expr.piBinders, Prod.mk.injEq] at h
    obtain ⟨rfl, hbody⟩ := h
    have hb : body.piBinders = (body.piBinders.1, Expr.sort u) := by rw [← hbody]
    simp only [List.length_cons, Expr.stripPis, stripPis_of_piBinders_sort hb,
      Option.map_some]
  | .sort u', bs, u, h => by
    simp only [Expr.piBinders, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [List.length_nil, Expr.stripPis, h2]
  | .bvar _, _, _, h | .fvar _ _, _, _, h | .const _ _, _, _, h
  | .app _ _, _, _, h | .lam _ _ _, _, _, h | .letE _ _ _, _, _, h
  | .lit _, _, _, h | .proj _ _ _, _, _, h => by
    simp [Expr.piBinders] at h

/-- The index count the auxiliary block records comes with the
telescope `checkSumTele`'s first branch needs. -/
theorem auxIdxCount_stripPis {nP nIdx : Nat} {ty : Expr}
    (h : auxIdxCount nP ty = some nIdx) :
    ∃ (bs : List (Expr × BinderMeta)) (u : Level),
      ty.stripPis (nP + nIdx) = some (bs, Expr.sort u) := by
  unfold auxIdxCount at h
  cases hpb : ty.piBinders with
  | mk bs body =>
    rw [hpb] at h
    cases body with
    | sort u =>
      simp only at h
      by_cases hle : nP ≤ bs.length
      · rw [if_pos hle] at h
        simp only [Option.some.injEq] at h
        obtain rfl := h
        have hlen : nP + (bs.length - nP) = bs.length := by omega
        rw [hlen]
        exact ⟨bs, u, stripPis_of_piBinders_sort hpb⟩
      · rw [if_neg hle] at h; exact nomatch h
    | _ => simp only at h; exact nomatch h

/-- The auxiliary block's formers ARE the elimination's types, position
by position, each with the index count `auxIdxCount` read off it. -/
theorem auxBlock_former {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (h : auxBlock p st = some b) :
    b.nP = p.nP ∧
    ∀ (i : Nat) (t : AuxType), st.types[i]? = some t →
      ∃ nIdx, b.formers[i]? = some ((⟨t.name, p.lps, t.type⟩ : ConstantVal), nIdx) ∧
        auxIdxCount p.nP t.type = some nIdx := by
  unfold auxBlock at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨formers, hformers, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  intro i t hi
  obtain ⟨fm, hfm, hft⟩ := mapM_option_inv hformers i t hi
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at hft
  obtain ⟨nIdx, hn, rfl⟩ := hft
  exact ⟨nIdx, hfm, hn⟩

/-- **THE FORMERS' IDENTITY THE MODEL TIER READS OFF THE RUN**
(task #279 K.10, widened by K.12).

Two of `DeclNestedRun`'s conjuncts — the auxiliary block and its install
in the scratch environment — already say that EVERY member of that block
(the block's own, and every copy the elimination minted) is stored with
the type `auxBlock` gave it, SYNTACTICALLY.  No annotation-stability
premise and no name test: the install's formers stage runs
`checkConstantValPre` on the whole block (the `auxRoute` grade), which
checks everything `checkConstantVal` checks and returns its input, and
`checkSumTele` returns it unchanged because the member's type is a
syntactic telescope ending in a sort — which is exactly what
`auxIdxCount` read off it when `auxBlock` recorded the index count.

`env₁ = consMutualFormers fms env` is how the stage stores it, so
`f.cvTa.type = t.type` IS the stored former's type. -/
theorem nestedCopyFormerType_eq {env envAux : Env} {p : NestedParts} {st : ElimState}
    {b : MutualBlock} {F : Nat}
    (hb : auxBlock p st = some b)
    (haux : checkMutualCore (m := CheckM) (fueledOps mode F) env b none true = .ok envAux) :
    ∀ (i : Nat) (t : AuxType), st.types[i]? = some t →
      ∃ (env₁ : Env) (fms : List MutualFormerA) (f : MutualFormerA),
        mutualFormers (fueledOps mode F) b.nP b.formers env true = .ok (env₁, fms) ∧
        env₁ = consMutualFormers fms env ∧
        fms[i]? = some f ∧ f.cvTa.type = t.type := by
  intro i t hi
  obtain ⟨hnP, hform⟩ := auxBlock_former hb
  obtain ⟨nIdx, hfi, hcnt⟩ := hform i t hi
  obtain ⟨-, -, -, -, env₁, fms, -, -, -, -, -, -, -, -, -, hformers, -⟩ :=
    checkMutualCore_inv haux
  obtain ⟨hchecks, henv₁⟩ := mutualFormers_inv hformers
  obtain ⟨bs, u, hstrip⟩ := auxIdxCount_stripPis hcnt
  refine ⟨env₁, fms, ?_⟩
  obtain ⟨f, hf, hft⟩ :=
    mutualFormerChecks_true_id hchecks i ⟨t.name, p.lps, t.type⟩ nIdx hfi
      ⟨bs, u, by rw [hnP]; exact hstrip⟩
  exact ⟨f, hformers, henv₁, hf, hft⟩

/-- **THE CONSTRUCTORS' IDENTITY** (K.12).  The same two conjuncts say
what the constructors' stage stores for EVERY constructor of the
auxiliary block: `normCtorValM`'s output on the MINTED constant — the
positivity normalisation and nothing else.  No annotation walk runs (the
grade), so the stored constructor is the minted one, with its type
replaced by the normalisation exactly where a member-mentioning field
domain reduced (`normCtorValM_true_stores` states that disjunction, and
the identity is its left arm).

The `whnf` behind the normalisation is NOT removable: at a λ-pin
(`DMap α (fun _ => PT α)`) the copied field is the redex
`(fun _ => PT α) k`, whose head is a `.lam`, and `mutualPositivity`
reads no member application there.

Only the install conjunct is needed — `b` is the block the run's
`auxBlock p st = some b` names, and `b.ctors` are the minted
constructors verbatim (`auxBlock` copies them out of `st.types`). -/
theorem nestedCopyCtorType_eq {env envAux : Env} {b : MutualBlock} {F : Nat}
    (haux : checkMutualCore (m := CheckM) (fueledOps mode F) env b none true = .ok envAux) :
    ∃ (env₁ : Env) (fms : List MutualFormerA) (ctorsA : List (ConstantVal × Nat))
      (sortss : List (List Level)) (isProp : Bool),
      mutualFormers (fueledOps mode F) b.nP b.formers env true = .ok (env₁, fms) ∧
      env₁ = consMutualFormers fms env ∧
      checkMutualCtors (fueledOps mode F) env₁ b fms isProp true b.ctors
        = .ok (ctorsA, sortss) ∧
      ctorsA.length = b.ctors.length ∧
      ∀ (j : Nat) (c : MutualCtor) (cA : ConstantVal × Nat),
        b.ctors[j]? = some c → ctorsA[j]? = some cA →
        normCtorValM (m := CheckM) (fueledOps mode F) env₁ b.memberNames b.nP c.nF
            c.cv c.cv true = .ok cA.1 ∧
          (cA.1 = c.cv ∨ ∃ ty', cA.1 = { c.cv with type := ty' }) ∧
          cA.1.type.projTablesOk env₁ = true := by
  obtain ⟨-, -, -, -, env₁, fms, f₀, -, ctorsA, sortss, -, -, -, -, -,
    hformers, -, -, -, -, hctors, -⟩ := checkMutualCore_inv haux
  obtain ⟨-, henv₁⟩ := mutualFormers_inv hformers
  refine ⟨env₁, fms, ctorsA, sortss, _, hformers, henv₁, hctors, ?_, ?_⟩
  · exact (checkMutualCtors_inv hctors).1
  · intro j c cA hc hcA
    obtain ⟨-, -, hall⟩ := checkMutualCtors_inv hctors
    obtain ⟨-, _sorts, -, hrun⟩ := hall j c cA hc hcA
    obtain ⟨hnorm, hproj, -⟩ := checkMutualCtor_true_norm hrun
    obtain ⟨hstores, hkeep⟩ := normCtorValM_true_stores hnorm
    exact ⟨hnorm, hstores, hkeep hproj⟩

/-! ### The restore stores the RESTORE, syntactically (task #279 K.19)

The restore stages run at the pre-annotated grade, so a stored restored
constant is `restoreNested R` of the auxiliary one and nothing else —
no annotation pass stands between them, and the model tier owes no
"annotation commutes with the restore" theorem. -/

/-- The restored CONSTRUCTORS, positionally. -/
theorem restoreCtors_id {env : Env} {R : RestoreTbl} {lps : List Name} {F : Nat} :
    ∀ {cs out : List (ConstantVal × Nat × Nat)},
      restoreCtors (m := CheckM) (fueledOps mode F) env R lps cs = .ok out →
      out.length = cs.length ∧
      ∀ (i : Nat) (c o : ConstantVal × Nat × Nat), cs[i]? = some c → out[i]? = some o →
        ∃ ty, restoreNested R c.1.type = .ok ty ∧
          o = ({ c.1 with levelParams := lps, type := ty }, c.2.1, c.2.2) := by
  intro cs
  induction cs with
  | nil =>
    intro out h
    simp only [restoreCtors, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨by rw [← h], fun i c o hc _ => by simp at hc⟩
  | cons hd rest ih =>
    intro out h
    obtain ⟨cvCa, nP, nF⟩ := hd
    unfold restoreCtors at h
    obtain ⟨ty, hty, h⟩ := exceptBind_ok h
    have hty' := nestedLift_ok hty
    obtain ⟨cvA, hpre, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    obtain ⟨hlen, hall⟩ := ih hrest
    refine ⟨by simp [hlen], ?_⟩
    intro i c o hc ho
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc ho
      obtain rfl := hc
      obtain rfl := ho
      exact ⟨ty, hty', by rw [checkConstantValPre_ok hpre]⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hc ho
      exact hall k c o hc ho

/-- **The restored CONSTRUCTORS went through a FRONT DOOR**, positionally
(task #315): each one is checked by `checkConstantValPre`, so the whole
`FrontDoorFacts` interface holds of it — and, the pre-annotated door
returning its input, the stored constant IS the restore of the
auxiliary one. -/
theorem restoreCtors_door {env : Env} {R : RestoreTbl} {lps : List Name} {F : Nat} :
    ∀ {cs out : List (ConstantVal × Nat × Nat)},
      restoreCtors (m := CheckM) (fueledOps mode F) env R lps cs = .ok out →
      out.length = cs.length ∧
      ∀ (i : Nat) (c o : ConstantVal × Nat × Nat), cs[i]? = some c → out[i]? = some o →
        ∃ ty, restoreNested R c.1.type = .ok ty ∧
          FrontDoorFacts mode F env { c.1 with levelParams := lps, type := ty } o.1 ∧
          o.2 = c.2 ∧
          o.1 = { c.1 with levelParams := lps, type := ty } := by
  intro cs
  induction cs with
  | nil =>
    intro out h
    simp only [restoreCtors, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨by rw [← h], fun i c o hc _ => by simp at hc⟩
  | cons hd rest ih =>
    intro out h
    obtain ⟨cvCa, nP, nF⟩ := hd
    unfold restoreCtors at h
    obtain ⟨ty, hty, h⟩ := exceptBind_ok h
    have hty' := nestedLift_ok hty
    obtain ⟨cvA, hpre, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    obtain ⟨hlen, hall⟩ := ih hrest
    refine ⟨by simp [hlen], ?_⟩
    intro i c o hc ho
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc ho
      obtain rfl := hc
      obtain rfl := ho
      exact ⟨ty, hty', FrontDoorFacts.ofPre hpre, rfl, checkConstantValPre_ok hpre⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hc ho
      exact hall k c o hc ho

/-- The restored CONSTRUCTORS' names, positionally: the restore keeps
every name. -/
theorem restoreCtors_names {env : Env} {R : RestoreTbl} {lps : List Name} {F : Nat}
    {cs out : List (ConstantVal × Nat × Nat)}
    (h : restoreCtors (m := CheckM) (fueledOps mode F) env R lps cs = .ok out) :
    out.map (·.1.name) = cs.map (·.1.name) := by
  obtain ⟨hlen, hall⟩ := restoreCtors_id h
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_map, List.getElem?_map]
  cases hc : cs[i]? with
  | none =>
    rw [List.getElem?_eq_none (by
      rw [hlen]; exact List.getElem?_eq_none_iff.mp hc)]
  | some c =>
    have hi : i < out.length := by
      rw [hlen]; exact (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨o, ho⟩ : ∃ o, out[i]? = some o := ⟨out[i], List.getElem?_eq_getElem hi⟩
    obtain ⟨_ty, -, hoeq⟩ := hall i c o hc ho
    rw [ho, hoeq]
    rfl

/-! ### The restored constructors' conses, as an environment extension
(task #315) -/

/-- A lookup past the restored constructors' conses of other names. -/
theorem consNestedCtors_find?_of_ne :
    ∀ {cs : List (ConstantVal × Nat × Nat)} {env : Env} {n : Name},
      (∀ c ∈ cs, c.1.name ≠ n) →
      (consNestedCtors cs env).find? n = env.find? n := by
  intro cs
  induction cs with
  | nil => intro _ _ _; rfl
  | cons hd rest ih =>
    intro env n hne
    obtain ⟨cv, nP, nF⟩ := hd
    show (consNestedCtors rest ⟨.ctorInfo cv nP nF :: env.consts⟩).find? n = _
    rw [ih (fun x hx => hne x (List.mem_cons_of_mem _ hx)), Env.find?_cons]
    exact if_neg (hne _ List.mem_cons_self)

/-- **The restored constructors' conses preserve every earlier
lookup**: their names are free at the environment they are consed onto
and pairwise distinct, so nothing is shadowed. -/
theorem consNestedCtors_findPreserved :
    ∀ {cs : List (ConstantVal × Nat × Nat)} {env : Env},
      (∀ c ∈ cs, env.find? c.1.name = none) →
      (cs.map (·.1.name)).Nodup →
      Semantics.FindPreserved env (consNestedCtors cs env) := by
  intro cs
  induction cs with
  | nil =>
    intro _ _ _
    exact fun h => h
  | cons hd rest ih =>
    intro env hfresh hnd
    obtain ⟨cv, nP, nF⟩ := hd
    rw [List.map_cons, List.nodup_cons] at hnd
    have hc : env.find? cv.name = none := hfresh _ List.mem_cons_self
    have hfresh' : ∀ g ∈ rest,
        (Env.mk (ConstantInfo.ctorInfo cv nP nF :: env.consts)).find? g.1.name = none := by
      intro g hg
      rw [Env.find?_cons, if_neg (fun hh => hnd.1 (by
        rw [show cv.name = g.1.name from hh]; exact List.mem_map_of_mem hg))]
      exact hfresh g (List.mem_cons_of_mem _ hg)
    intro n ci h
    show (consNestedCtors rest ⟨.ctorInfo cv nP nF :: env.consts⟩).find? n = some ci
    exact ih hfresh' hnd.2 (Env.find?_cons_of_fresh hc h)

/-- The restored RECURSOR TYPES, positionally: the level parameters are
the auxiliary recursor's and the type is the restore of its type. -/
theorem restoreRecTys_id {env : Env} {R : RestoreTbl} {lps : List Name} {F : Nat} :
    ∀ {names : List Name} {as : List AuxStored} {out : List ConstantVal},
      restoreRecTys (m := CheckM) (fueledOps mode F) env R lps names as = .ok out →
      out.length = as.length ∧
      ∀ (i : Nat) (a : AuxStored) (o : ConstantVal), as[i]? = some a → out[i]? = some o →
        o.levelParams = a.cvRa.levelParams ∧ restoreNested R a.cvRa.type = .ok o.type := by
  intro names as
  induction as generalizing names with
  | nil =>
    intro out h
    simp only [restoreRecTys, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨by rw [← h]; rfl, fun i a o ha _ => by simp at ha⟩
  | cons a rest ih =>
    intro out h
    unfold restoreRecTys at h
    obtain ⟨ty, hty, h⟩ := exceptBind_ok h
    have hty' := nestedLift_ok hty
    obtain ⟨cvA, hpre, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    obtain ⟨hlen, hall⟩ := ih hrest
    refine ⟨by simp [hlen], ?_⟩
    intro i a' o ha ho
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha ho
      obtain rfl := ha
      obtain rfl := ho
      rw [checkConstantValPre_ok hpre]
      exact ⟨rfl, hty'⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at ha ho
      exact hall k a' o ha ho

/-- The restored RULES, positionally: the stored right-hand side is the
restore of the auxiliary one, and the constructor's name and the rule's
fields are the ones the restore table names. -/
theorem restoreRules_id {envR : Env} {R : RestoreTbl} {lps : List Name} {recName : Name}
    {isMimic : Bool} {recTy : Expr} {mI rP F : Nat} :
    ∀ {rules out : List RecRule},
      restoreRules (m := CheckM) (fueledOps mode F) envR R lps recName isMimic recTy mI rP
          rules = .ok out →
      out.length = rules.length ∧
      ∀ (i : Nat) (rl o : RecRule), rules[i]? = some rl → out[i]? = some o →
        restoreNested R rl.rhs = .ok o.rhs := by
  intro rules
  induction rules with
  | nil =>
    intro out h
    simp only [restoreRules, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨by rw [← h], fun i rl o hr _ => by simp at hr⟩
  | cons rl rest ih =>
    intro out h
    unfold restoreRules at h
    obtain ⟨rhsA, hrhs, h⟩ := exceptBind_ok h
    have hrhs' := nestedLift_ok hrhs
    by_cases h1 : (rhsA.allLevelParamsDefined lps && rhsA.constsResolve envR &&
        rhsA.looseBVarsBounded 0 && !rhsA.hasFvar) = true
    case neg => rw [if_neg h1] at h; close_throw
    rw [if_pos h1] at h
    try simp only [bind, Except.bind] at h
    by_cases h2 : rhsA.projTablesOk envR = true
    case neg => rw [if_neg h2] at h; close_throw
    rw [if_pos h2] at h
    try simp only [bind, Except.bind] at h
    obtain ⟨_ty, _hty, h⟩ := exceptBind_ok h
    try simp only at h
    by_cases h3 : (!isMimic || (R.ctorPins.any fun q => q.1 == rl.ctor)) = true
    case neg => rw [if_neg h3] at h; close_throw
    rw [if_pos h3] at h
    try simp only [bind, Except.bind] at h
    -- K.24: the rule's constructor must be a stored constructor here
    split at h
    case h_2 => close_throw
    rename_i cvj cnP cnF hfind
    try simp only [pure, Except.pure] at h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [Except.ok.injEq] at h
    obtain rfl := h
    obtain ⟨hlen, hall⟩ := ih hrest
    refine ⟨by simp [hlen], ?_⟩
    intro i rl' o hr ho
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr ho
      obtain rfl := hr
      obtain rfl := ho
      simpa using hrhs'
    | succ k =>
      simp only [List.getElem?_cons_succ] at hr ho
      exact hall k rl' o hr ho

/-! ### Freshness, for the η-families' closure (task #279 K.20) -/

/-- A lookup answers with a constant OF THAT NAME. -/
theorem Env.find?_name {env : Env} {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  unfold Env.find? at h
  have := List.find?_some h
  exact beq_iff_eq.mp this

/-- The pre-annotated front door's FIRST guard: the name is free. -/
theorem checkConstantValPre_fresh {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvA) :
    env.find? cv.name = none := by
  unfold checkConstantValPre at h
  by_cases h1 : (env.find? cv.name).isSome = true
  case pos => rw [if_pos h1] at h; close_throw
  simpa using Option.not_isSome_iff_eq_none.mp (by simpa using h1)

/-- Every member of a block checked at `auxRoute` has a name the
environment does not carry. -/
theorem mutualFormerChecks_true_fresh {nP F : Nat} {env : Env} :
    ∀ {formers : List (ConstantVal × Nat)} {fms : List MutualFormerA},
      mutualFormerChecks (fueledOps mode F) env nP true formers = .ok fms →
      ∀ (i : Nat) (cv : ConstantVal) (nIdx : Nat),
        formers[i]? = some (cv, nIdx) → env.find? cv.name = none := by
  intro formers
  induction formers with
  | nil => intro fms _h i cv nIdx hi; exact absurd hi (by simp)
  | cons hd rest ih =>
    intro fms h i cv nIdx hi
    obtain ⟨cv₀, nIdx₀⟩ := hd
    obtain ⟨cvTa₀, cvTa, s, fs, hfront, -, hrec, -⟩ := mutualFormerChecks_true_cons h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      exact checkConstantValPre_fresh hfront
    | succ k =>
      simp only [List.getElem?_cons_succ] at hi
      exact ih hrec k cv nIdx hi

/-- The restored CONSTRUCTORS' names are free at the environment they
are checked at. -/
theorem restoreCtors_fresh {env : Env} {R : RestoreTbl} {lps : List Name} {F : Nat} :
    ∀ {cs out : List (ConstantVal × Nat × Nat)},
      restoreCtors (m := CheckM) (fueledOps mode F) env R lps cs = .ok out →
      ∀ o ∈ out, env.find? o.1.name = none := by
  intro cs
  induction cs with
  | nil =>
    intro out h o ho
    simp only [restoreCtors, pure, Except.pure, Except.ok.injEq] at h
    rw [← h] at ho; exact absurd ho (by simp)
  | cons hd rest ih =>
    intro out h o ho
    obtain ⟨cvCa, nP, nF⟩ := hd
    unfold restoreCtors at h
    obtain ⟨ty, -, h⟩ := exceptBind_ok h
    obtain ⟨cvA, hpre, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    rcases List.mem_cons.mp ho with rfl | ho
    · show env.find? cvA.name = none
      rw [checkConstantValPre_ok hpre]
      exact checkConstantValPre_fresh hpre
    · exact ih hrest o ho

/-- The restored RECURSOR types' names are free at the environment they
are checked at. -/
theorem restoreRecTys_fresh {env : Env} {R : RestoreTbl} {lps : List Name} {F : Nat} :
    ∀ {names : List Name} {as : List AuxStored} {out : List ConstantVal},
      restoreRecTys (m := CheckM) (fueledOps mode F) env R lps names as = .ok out →
      ∀ o ∈ out, env.find? o.name = none := by
  intro names as
  induction as generalizing names with
  | nil =>
    intro out h o ho
    simp only [restoreRecTys, pure, Except.pure, Except.ok.injEq] at h
    rw [← h] at ho; exact absurd ho (by simp)
  | cons a rest ih =>
    intro out h o ho
    unfold restoreRecTys at h
    obtain ⟨ty, -, h⟩ := exceptBind_ok h
    obtain ⟨cvA, hpre, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    rcases List.mem_cons.mp ho with rfl | ho
    · rw [checkConstantValPre_ok hpre]
      exact checkConstantValPre_fresh hpre
    · exact ih hrest o ho

/-- The read-back, positionally. -/
theorem auxStoredAll_get {envAux : Env} {b : MutualBlock} :
    ∀ {k : Nat} {stored : List AuxStored}, auxStoredAll envAux b k = some stored →
      stored.length = k ∧
      ∀ (i : Nat) (a : AuxStored), stored[i]? = some a → auxStored? envAux b i = some a := by
  intro k
  induction k with
  | zero =>
    intro stored h
    simp only [auxStoredAll, Option.some.injEq] at h
    exact ⟨by rw [← h]; rfl, fun i a ha => by rw [← h] at ha; exact absurd ha (by simp)⟩
  | succ k ih =>
    intro stored h
    simp only [auxStoredAll, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨earlier, hearlier, a, ha, rfl⟩ := h
    obtain ⟨hlen, hall⟩ := ih hearlier
    refine ⟨by simp [hlen], ?_⟩
    intro i a' hi
    by_cases hlt : i < earlier.length
    · rw [List.getElem?_append_left hlt] at hi
      exact hall i a' hi
    · have : i = earlier.length := by
        have := (List.getElem?_eq_some_iff.mp hi).1
        simp at this
        omega
      subst this
      rw [List.getElem?_append_right (by omega)] at hi
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hi
      obtain rfl := hi
      rw [hlen]
      exact ha

/-! ### The restored rules' constructors are stored (task #279 K.24) -/

/-- **Every restored rule's constructor is a STORED CONSTRUCTOR** at the
environment the rules were restored at: `restoreRules` reads its
parameter count with `envR.find?` and now REJECTS when that is not a
`ctorInfo`, where it used to fall back on the stream's own count (K.24 —
official reads the same record with `env.get`, which throws). -/
theorem restoreRules_ctorStored {envR : Env} {R : RestoreTbl} {lps : List Name}
    {recName : Name} {isMimic : Bool} {recTy : Expr} {mI rP F : Nat} :
    ∀ {rules out : List RecRule},
      restoreRules (m := CheckM) (fueledOps mode F) envR R lps recName isMimic recTy mI rP
          rules = .ok out →
      ∀ o ∈ out, ∃ (cv : ConstantVal) (n nF : Nat),
        envR.find? o.ctor = some (.ctorInfo cv n nF) := by
  intro rules
  induction rules with
  | nil =>
    intro out h o ho
    simp only [restoreRules, pure, Except.pure, Except.ok.injEq] at h
    rw [← h] at ho; exact absurd ho (by simp)
  | cons rl rest ih =>
    intro out h o ho
    unfold restoreRules at h
    obtain ⟨rhsA, _hrhs, h⟩ := exceptBind_ok h
    by_cases h1 : (rhsA.allLevelParamsDefined lps && rhsA.constsResolve envR &&
        rhsA.looseBVarsBounded 0 && !rhsA.hasFvar) = true
    case neg => rw [if_neg h1] at h; close_throw
    rw [if_pos h1] at h
    try simp only [bind, Except.bind] at h
    by_cases h2 : rhsA.projTablesOk envR = true
    case neg => rw [if_neg h2] at h; close_throw
    rw [if_pos h2] at h
    try simp only [bind, Except.bind] at h
    obtain ⟨_ty, _hty, h⟩ := exceptBind_ok h
    try simp only at h
    by_cases h3 : (!isMimic || (R.ctorPins.any fun q => q.1 == rl.ctor)) = true
    case neg => rw [if_neg h3] at h; close_throw
    rw [if_pos h3] at h
    try simp only [bind, Except.bind] at h
    split at h
    case h_2 => close_throw
    rename_i cvj cnP cnF hfind
    try simp only [pure, Except.pure] at h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [Except.ok.injEq] at h
    obtain rfl := h
    rcases List.mem_cons.mp ho with rfl | ho
    · exact ⟨cvj, cnP, cnF, by simpa using hfind⟩
    · exact ih hrest o ho

/-- A `ctorInfo` found past the rule-less provision was found below it:
the provision adds only recursors. -/
theorem provisionNestedRecs_find?_ctorInfo :
    ∀ (l : List (ConstantVal × Nat × Nat)) {env : Env} {n : Name} {cv : ConstantVal}
      {nP nF : Nat},
      (provisionNestedRecs l env).find? n = some (.ctorInfo cv nP nF) →
      env.find? n = some (.ctorInfo cv nP nF) := by
  intro l
  induction l with
  | nil => intro env n cv nP nF h; exact h
  | cons hd rest ih =>
    intro env n cv nP nF h
    obtain ⟨cvRa, mI, rP⟩ := hd
    have h' := ih h
    unfold Env.find? at h' ⊢
    simp only [List.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- **NO BLOCK MEMBER CARRIES A COPY'S NAME** (task #279 K.18, the model
lane's question).

The front guard is NOT what gives this: `check_no_nested_aux` rejects a
block whose declared TYPES MENTION a `_nested`-prefixed constant, not a
declaration NAMED one — official skips a taken name at the mint
(`mk_unique_name`) rather than failing, and this route follows it.  What
gives it is the auxiliary block's own shape check: `checkMutualCore`
opens with `mutualShapeOk`, whose first conjunct is
`b.blockNames.Nodup` — and `b.blockNames` is every member name, every
constructor name and every recursor name of the block, the stream's
members and the minted copies alike.  A stream member named like a copy
would put the same name twice in that list and the install would REJECT.

So the fact is carried by the run relation's `checkMutualCore … = .ok
envAux` conjunct, and this is how to read it off. -/
theorem nestedBlockNames_nodup {env envAux : Env} {b : MutualBlock} {F : Nat}
    (haux : checkMutualCore (m := CheckM) (fueledOps mode F) env b none true = .ok envAux) :
    b.blockNames.Nodup := (checkMutualCore_inv haux).1

/-! ### THE TWO COPY-FIELD ARMS' SHARED WALK, READ COMPONENTWISE (task #315 K.60, K.63)

`nestedCopyFieldsAt` runs K.60's and K.63's guards in ONE pass and
returns the pair; `nestedCopyPinFieldsAt` and `nestedCopyReflFieldsAt`
are its two components.  These are the two extraction lemmas the
inversions use where an `all`-shaped walk would use
`List.all_eq_true`. -/

theorem allPair_fst_mem {α : Type} {f : α → Bool × Bool} :
    ∀ {l : List α}, (allPair l f).1 = true → ∀ a ∈ l, (f a).1 = true
  | [], _, _, ha => absurd ha (by simp)
  | b :: bs, h, a, ha => by
    simp only [allPair, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact h.1
    · exact allPair_fst_mem h.2 a ha'

theorem allPair_snd_mem {α : Type} {f : α → Bool × Bool} :
    ∀ {l : List α}, (allPair l f).2 = true → ∀ a ∈ l, (f a).2 = true
  | [], _, _, ha => absurd ha (by simp)
  | b :: bs, h, a, ha => by
    simp only [allPair, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact h.1
    · exact allPair_snd_mem h.2 a ha'

/-- **K.46's grouped gate, inverted**: `nestedPinChecks` bundles K.26,
K.32, K.37 and K.41 so that the field kinds and the reference edge list
are computed ONCE, and this reads the four conjuncts back in the shape
`DeclNestedRun` records them.  At `.trusted` the group does not run and
every `certOnly` is `true`; at `.verified` each `unless` is its own
clause, as before. -/
theorem nestedPinChecks_inv {ops : CheckerOps CheckM} {env envN : Env} {p : NestedParts}
    {b : MutualBlock} {st : ElimState} {stored : List AuxStored} {u : Unit}
    (h : nestedPinChecks ops env envN p b st stored = .ok u) :
    certOnly ops.mode (nestedCopyTargetsOk env p b st stored) = true ∧
      certOnly ops.mode (nestedPinKindsOk p b st stored) = true ∧
      certOnly ops.mode (nestedPinRankOk env p b st stored) = true ∧
      certOnly ops.mode (nestedPinRootPairOk env p b st stored) = true ∧
      -- **K.57**: a reference that LEAVES the instance goes to a
      -- container declared strictly earlier
      certOnly ops.mode (nestedPinOrderOk env p b st stored) = true ∧
      (ops.mode.verifiedChecks = true →
        ∃ (jobs : List (Nat × Expr × Expr)) (ws : List Expr),
          nestedOrdDomPairs env p st stored (nestedPinKinds p b stored) = some jobs ∧
          nestedOrdNorms ops envN b.memberNames jobs = .ok ws ∧
          ws = jobs.map (·.2.2)) ∧
      -- **K.51**: the same walk at the PIN targets, whose stored domain
      -- is headed by the mimic, so the normalisation's output is
      -- REWRITTEN before the comparison
      (ops.mode.verifiedChecks = true →
        ∃ (params : List Expr) (pbs₀ : List (Expr × BinderMeta))
          (jobsP : List (Nat × Expr × Expr)) (wsP : List Expr),
          nestedRewriteData p st = some (params, pbs₀) ∧
          nestedPinDomPairs env p st stored (nestedPinKinds p b stored) = some jobsP ∧
          nestedPinNorms ops envN b.memberNames jobsP = .ok wsP ∧
          nestedPinRewrites env p st params pbs₀ jobsP wsP = true) ∧
      -- **K.60**: a container's nested field lands on a block pin.
      -- UNCONDITIONAL — it stands before the mode test, because its
      -- consumer reads it in every mode
      nestedCopyPinFieldsOk env p b st stored = true ∧
      -- **K.63**: a container's REFLEXIVE nested field lands on a block
      -- pin — K.60's guard one `Π`-tower down, on the same walk
      nestedCopyReflFieldsOk env p b st stored = true ∧
      -- **K.61**: the container instance map, and the own-pin fields'
      -- targets.  UNCONDITIONAL, for K.60's reason
      nestedInstMapOk env p b st stored = true ∧
      -- **K.62**: a rewritten ORDINARY field's target is outside the
      -- instance.  UNCONDITIONAL, for K.60's reason
      nestedOrdOutsideOk env p b st stored = true ∧
      -- **K.67**: and it IS the owning container's own class, imaged.
      -- K.62's positive twin at the same guard; UNCONDITIONAL, for
      -- K.60's reason
      nestedOrdTargetOk env p b st stored = true ∧
      -- **K.68**: and it is THIS block's own class, by its own
      -- recomputation — K.67's self-relative twin, the half a LATER
      -- block reads of this one
      nestedOrdSelfTargetOk env p b st stored = true := by
  unfold nestedPinChecks at h
  simp only at h
  by_cases hcpf : (nestedCopyFieldsAt env p st (nestedPinKinds p b stored)).1 = true
  case neg => rw [if_pos (by simpa using hcpf)] at h; close_throw
  rw [if_neg (by simpa using hcpf)] at h
  by_cases hcrf : (nestedCopyFieldsAt env p st (nestedPinKinds p b stored)).2 = true
  case neg => rw [if_pos (by simpa using hcrf)] at h; close_throw
  rw [if_neg (by simpa using hcrf)] at h
  by_cases him : nestedInstMapOkAt env p st (nestedInstMaps env st)
      (nestedPinKinds p b stored) = true
  case neg => rw [if_pos (by simpa using him)] at h; close_throw
  rw [if_neg (by simpa using him)] at h
  by_cases hout : nestedOrdOutsideAt st (nestedInstMaps env st)
      (nestedPinEdgesAt env p st stored (nestedPinKinds p b stored)) = true
  case neg => rw [if_pos (by simpa using hout)] at h; close_throw
  rw [if_neg (by simpa using hout)] at h
  by_cases htgt : nestedOrdTargetAt env p st (nestedInstMaps env st)
      (nestedPinKinds p b stored) = true
  case neg => rw [if_pos (by simpa using htgt)] at h; close_throw
  rw [if_neg (by simpa using htgt)] at h
  by_cases hstgt : nestedOrdSelfTargetAt env p st (nestedPinKinds p b stored) = true
  case neg => rw [if_pos (by simpa using hstgt)] at h; close_throw
  rw [if_neg (by simpa using hstgt)] at h
  rcases Bool.eq_false_or_eq_true ops.mode.verifiedChecks with hv | hv
  · -- `.verified`: each `unless` is its own clause, as before
    simp only [hv, Bool.not_true, Bool.false_eq_true, if_false] at h
    split at h
    · close_throw
    · rename_i htg
      have htg' : nestedCopyTargetsAt env p st stored (nestedPinKinds p b stored) = true := by
        simpa using htg
      split at h
      · close_throw
      · rename_i hkd
        have hkd' : nestedPinKindsAt p st (nestedPinKinds p b stored) = true := by
          simpa using hkd
        split at h
        · close_throw
        · rename_i hrk
          have hrk' : nestedPinRankAt st
              (nestedPinEdgesAt env p st stored (nestedPinKinds p b stored)) = true := by
            simpa using hrk
          split at h
          · close_throw
          · rename_i hrh
            have hrh' : nestedPinRootPairAt env st
                (nestedPinRootGroupAt p st (nestedPinInstAt st
                  (nestedPinEdgesAt env p st stored (nestedPinKinds p b stored)))) = true := by
              simpa using hrh
            split at h
            case isTrue => close_throw
            rename_i hord
            have hord' : nestedPinOrderAt env p st stored
                (nestedPinKinds p b stored) = true := by
              simpa using hord
            obtain ⟨jobs, hjobs, h⟩ := exceptBind_ok h
            obtain ⟨ws, hws, h⟩ := exceptBind_ok h
            by_cases hcmp : (ws == jobs.map (·.2.2)) = true
            case neg => rw [if_neg hcmp] at h; close_throw
            rw [if_pos hcmp] at h
            obtain ⟨pd, hpd, h⟩ := exceptBind_ok h
            obtain ⟨jobsP, hjobsP, h⟩ := exceptBind_ok h
            obtain ⟨wsP, hwsP, h⟩ := exceptBind_ok h
            by_cases hrw : nestedPinRewrites env p st pd.1 pd.2 jobsP wsP = true
            case neg => rw [if_neg (by simpa using hrw)] at h; close_throw
            exact ⟨by simp [certOnly, nestedCopyTargetsOk, htg'],
              by simp [certOnly, nestedPinKindsOk, hkd'],
              by simp [certOnly, nestedPinRankOk, nestedPinEdges, hrk'],
              by simp [certOnly, nestedPinRootPairOk, nestedPinRootGroup, nestedPinInstOf,
                nestedPinEdges, hrh'],
              by simp [certOnly, nestedPinOrderOk, hord'],
              fun _ => ⟨jobs, ws, unwrapOr_ok hjobs, hws, by simpa using hcmp⟩,
              fun _ => ⟨pd.1, pd.2, jobsP, wsP, unwrapOr_ok hpd, unwrapOr_ok hjobsP,
                hwsP, hrw⟩, hcpf, hcrf, him, hout, htgt, hstgt⟩
  · -- `.trusted`: the group does not run, and every `certOnly` is `true`
    exact ⟨by simp [certOnly, hv], by simp [certOnly, hv], by simp [certOnly, hv],
      by simp [certOnly, hv], by simp [certOnly, hv],
      fun hv' => absurd hv' (by simp [hv]),
      fun hv' => absurd hv' (by simp [hv]), hcpf, hcrf, him, hout, htgt, hstgt⟩

/-- **The nested chain's FRONT half**: official's two syntactic guards,
the elimination on the annotated inputs, the mimic count, the minted
names' freshness, the containers' facts, the pins' components, the
auxiliary block and its install — down to the point where
`checkNestedRest` takes over.

The route's inversion is TWO declarations because as one it sat at the
elaborator's heartbeat budget (see `checkNestedRest`'s docstring); they
are composed by `checkNested_inv`, whose statement is unchanged. -/
private theorem checkNested_inv_front {env envOut : Env} {p : NestedParts} {F : Nat}
    (h : checkNested (m := CheckM) (fueledOps mode F) env p = .ok envOut) :
    (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all
        (fun t => !t.mentionsNestedAux)) = true ∧
    uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true ∧
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env)
      (fmsA ctorsA : List ConstantVal),
      -- THE INPUTS, ANNOTATED (K.12): the formers as the install will
      -- store them, the constructors at the environment holding those
      -- formers — so every piece the elimination builds a copy out of is
      -- annotated, and no annotation pass is left to run on a copy
      nestedAnnotFormers (m := CheckM) (fueledOps mode F) env p.nP p.formers = .ok fmsA ∧
      nestedAnnotCtors (m := CheckM) (fueledOps mode F) (nestedFormerEnv fmsA env) p.ctors
        = .ok ctorsA ∧
      -- the elimination on those, and the mimic count against the
      -- stream's records
      elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA) = .ok st ∧
      st.pins.length = p.numNested ∧
      -- every MINTED name is free in the pre-block environment
      copiesFresh env p.k st = true ∧
      -- the CONTAINERS' facts (K.14): uniform occurrences of the group in
      -- the stored constructors, and the two recursor facts at every member
      certOnly mode (nestedContainersOk env st.pins) = true ∧
      -- **THE PINS' COMPONENTS REWRITE** (lane L-E's request): every
      -- component of every pin's argument spine goes through the
      -- elimination's own `replaceAllNested` at the final state.
      -- UNCONDITIONAL: the model's `recF`, `es` and `ordF`-left arms
      -- read the rewritten components in every mode
      nestedPinCompsOk env p st = true ∧
      -- the auxiliary mutual block, checked in a SCRATCH environment
      auxBlock p st = some b ∧
      checkMutualCore (m := CheckM) (fueledOps mode F) env b none true = .ok envAux ∧
      -- and the SECOND STAGE, at what the first one produced
      checkNestedRest (m := CheckM) (fueledOps mode F) env p st b envAux
        = .ok envOut := by
  unfold checkNested at h
  simp only at h
  by_cases hg₀ : (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all (fun t => !t.mentionsNestedAux)) = true
  case neg => rw [if_neg hg₀] at h; close_throw
  rw [if_pos hg₀] at h
  try simp only [bind, Except.bind] at h
  by_cases hg₁ : uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true
  case neg => rw [if_neg hg₁] at h; close_throw
  rw [if_pos hg₁] at h
  refine ⟨hg₀, hg₁, ?_⟩
  try simp only [bind, Except.bind] at h
  obtain ⟨fmsA, hfmsA, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨ctorsA, hctorsA, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨st, helim, h⟩ := exceptBind_ok h
  have helim' := nestedLift_ok helim
  try simp only at h
  by_cases hcnt : (st.pins.length == p.numNested) = true
  case neg => rw [if_neg hcnt] at h; close_throw
  rw [if_pos hcnt] at h
  try simp only [bind, Except.bind] at h
  by_cases hfresh : copiesFresh env p.k st = true
  case neg => rw [if_neg hfresh] at h; close_throw
  rw [if_pos hfresh] at h
  try simp only [bind, Except.bind] at h
  by_cases hcont : certOnly (fueledOps mode F).mode (nestedContainersOk env st.pins) = true
  case neg => rw [if_neg hcont] at h; close_throw
  rw [if_pos hcont] at h
  try simp only [bind, Except.bind] at h
  by_cases hcomp : nestedPinCompsOk env p st = true
  case neg => rw [if_neg hcomp] at h; close_throw
  rw [if_pos hcomp] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  have hb' := unwrapOr_ok hb
  try simp only at h
  by_cases hidx : (p.formers.map (·.2) == (b.formers.take p.k).map (·.2)) = true
  case neg => rw [if_neg hidx] at h; close_throw
  rw [if_pos hidx] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨envAux, haux, h⟩ := exceptBind_ok h
  try simp only at h
  exact ⟨st, b, envAux, fmsA, ctorsA,
    hfmsA, hctorsA, helim', beq_iff_eq.mp hcnt, hfresh, hcont, hcomp, hb', haux, h⟩

/-- **The nested chain's SECOND half**: `checkNestedRest`'s own stages —
the auxiliary block's read-back, the pins' scope and their three typings,
the certification group, the two positivity walks, the restore of
constructors, recursor types and rules, the projection tables and the
three post-checks.

`hcont` is the front half's containers' fact, whose left conjunct is the
pins' structural distinctness recorded here; nothing else crosses the
cut. -/
private theorem checkNested_inv_rest {env envOut : Env} {p : NestedParts} {F : Nat}
    {st : ElimState} {b : MutualBlock} {envAux : Env}
    (hcont : certOnly mode (nestedContainersOk env st.pins) = true)
    (h : checkNestedRest (m := CheckM) (fueledOps mode F) env p st b envAux
      = .ok envOut) :
    ∃ (stored : List AuxStored)
      (ctorsR : List (List (ConstantVal × Nat × Nat)))
      (cvRms cvRns : List ConstantVal)
      (rulesM rulesN : List (List RecRule)),
      auxStoredAll envAux b b.k = some stored ∧
      -- `pinsClosed`: every pin, abstracted over the parameters, is
      -- fvar-free with its loose bvars inside the telescope
      pinsClosed p.nP st.pins = true ∧
      -- `pinsOkAux`: the pins — the elimination's own, annotated terms
      -- opened at the block's parameter variables — typed at the SCRATCH
      -- environment
      nestedPinsOk (m := CheckM) (fueledOps mode F) envAux p.nP st.pins = .ok () ∧
      -- the restored formers are fresh and carry no η bit (K.20)
      (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone)
        = true ∧
      -- THE COPIES' SOURCES (K.28): every minted auxiliary type is
      -- `mkCopy`'s output at the `(J, lvls, Ds)` it records, so the
      -- copy-instantiation identities are a field read
      certOnly mode (nestedCopySrcOk env p st) = true ∧
      -- THE PINS ARE STRUCTURALLY DISTINCT (K.15 (2), named at K.31):
      -- read off `nestedContainersOk`'s first conjunct, so this costs no
      -- second check — what `replaceAllNested`'s `find?` rewrite needs
      certOnly mode (pinsDistinct st.pins) = true ∧
      -- THE PINS' MINT GROUPS (K.29): the segment, its size, the
      -- member order, and the group's shared `lvls`/`Ds`
      certOnly mode (nestedGroupsOk env p st) = true ∧
      -- A PIN'S COMPONENTS MENTION A MEMBER (K.44): lane L-E's
      -- `nestMention`, whose witness the elimination's record does not pin
      certOnly mode (nestedPinMentionOk p st) = true ∧
      -- THE PINS' SCOPE (K.30): the pins' free variables are the first
      -- former's openers, annotation included, and no loose bvar
      certOnly mode (pinsScoped p.nP st) = true ∧
      -- THE PINS' LEVELS (K.48): every level parameter a pin mentions is
      -- the block's own — `ContainerModeled.pinParams` at the nested site
      certOnly mode (pinsLevelsOk p.lps st.pins) = true ∧
      -- THE COPIES' RECURSIVE TARGETS (K.32): a group-recursive copy
      -- field comes from the container's own recursion at the spine
      certOnly mode (nestedCopyTargetsOk env p b st stored) = true ∧
      -- THE FIELD KINDS (K.26): the auxiliary block's stored fields are
      -- classified `.ordinary`, `.recursive` or `.reflexive`, and
      -- `nestedPinKinds p b stored` is that classification
      certOnly mode (nestedPinKindsOk p b st stored) = true ∧
      -- THE AUXILIARY APPLICATIONS (K.35): the restore's
      -- `args.drop nP` precondition, at the read-back recursor types
      -- and rules
      certOnly mode (nestedAuxAppsOk p st stored) = true ∧
      -- THE PINS' CONTAINER INSTANCES AND RANK (K.37): the model's
      -- induction measure for step (iii)
      certOnly mode (nestedPinRankOk env p b st stored) = true ∧
      -- THE MINT PARENTS (K.40)
      certOnly mode (nestedPinParentOk p st) = true ∧
      -- THE PIN PAIRING AT A NOT-OWN EDGE (K.41): all four of `ClassPin`'s
      certOnly mode (nestedPinRootPairOk env p b st stored) = true ∧
      -- THE NOT-OWN REFERENCES' ORDER (K.57): a reference that leaves the
      -- instance goes to a container declared strictly earlier — the
      -- model's step (iii) inducts on it at a constant-headed field
      certOnly mode (nestedPinOrderOk env p b st stored) = true ∧
      -- THE POSITIVITY NORMALISATION ON THE MINTED COPY (K.42): at every
      -- ORDINARY field of every copy's constructor, the stored domain IS
      -- the normalisation of the MINTED one — lane L-B's `ordF`-left arm
      (mode.verifiedChecks = true →
        ∃ (jobs : List (Nat × Expr × Expr)) (ws : List Expr),
          nestedOrdDomPairs env p st stored (nestedPinKinds p b stored) = some jobs ∧
          nestedOrdNorms (m := CheckM) (fueledOps mode F)
              (consNestedFormers (stored.take p.k) env) b.memberNames jobs = .ok ws ∧
          ws = jobs.map (·.2.2)) ∧
      -- THE SAME WALK AT A PIN TARGET, REWRITTEN (K.51): there the
      -- stored domain is headed by the MIMIC and the minted one by the
      -- CONTAINER, so the normalisation's output is rewritten — by the
      -- elimination's own `replaceAllNested`, at the FINAL state, which
      -- therefore mints nothing — before the comparison
      (mode.verifiedChecks = true →
        ∃ (params : List Expr) (pbs₀ : List (Expr × BinderMeta))
          (jobsP : List (Nat × Expr × Expr)) (wsP : List Expr),
          nestedRewriteData p st = some (params, pbs₀) ∧
          nestedPinDomPairs env p st stored (nestedPinKinds p b stored) = some jobsP ∧
          nestedPinNorms (m := CheckM) (fueledOps mode F)
              (consNestedFormers (stored.take p.k) env) b.memberNames jobsP = .ok wsP ∧
          nestedPinRewrites env p st params pbs₀ jobsP wsP = true) ∧
      -- **A CONTAINER'S NESTED FIELD LANDS ON A BLOCK PIN** (K.60):
      -- at a container field headed by another stored container whose
      -- parameter part carries one of the container's own members, the
      -- copy's corresponding field is classified `.recursive` into a
      -- PIN.  K.32's twin, running the other way; UNCONDITIONAL, since
      -- the model's `pinF` arm reads it in every mode
      nestedCopyPinFieldsOk env p b st stored = true ∧
      -- **A CONTAINER'S REFLEXIVE NESTED FIELD LANDS ON A BLOCK PIN**
      -- (K.63): K.60's guard one `Π`-tower down, where K.60 claims
      -- nothing by construction; the same walk computes both
      nestedCopyReflFieldsOk env p b st stored = true ∧
      -- **THE CONTAINER INSTANCE MAP** (K.61): every own pin of every
      -- pin's container, instantiated at that pin's own levels and
      -- components, IS a block pin, and a copy's field at one of those
      -- own pins records the map's value as its target.  K.41's
      -- converse, and a FUNCTION where K.41 has only a covering
      nestedInstMapOk env p b st stored = true ∧
      -- **A REWRITTEN ORDINARY FIELD LEAVES THE INSTANCE** (K.62): at
      -- an `ordF`-right edge the recorded target is outside the
      -- instance map's image
      nestedOrdOutsideOk env p b st stored = true ∧
      -- **AND IT IS THE OWNING CONTAINER'S OWN CLASS, IMAGED** (K.67):
      -- K.62's positive twin at the same guard, recomputed from the
      -- container's stored constructor at the owner's own components
      nestedOrdTargetOk env p b st stored = true ∧
      -- **K.68**: and it is THIS block's own class, by its own
      -- recomputation
      nestedOrdSelfTargetOk env p b st stored = true ∧
      -- POST-CHECK (a) A THIRD TIME (K.30): the pins typed at the
      -- environment holding the RESTORED formers
      nestedPinsOk (m := CheckM) (fueledOps mode F)
          (consNestedFormers (stored.take p.k) env) p.nP st.pins = .ok () ∧
      -- **THE PINS' CONSTANTS RESOLVE** (K.64): at that same
      -- environment.  UNCONDITIONAL: the consumer — a container's
      -- pins' components' READINGS, which cross a later install only
      -- under the projection guard — reads it in every mode
      pinsResolve (consNestedFormers (stored.take p.k) env) st.pins = true ∧
      -- the restored constructors, at the environment holding the formers
      (stored.take p.k).mapM (fun a =>
          restoreCtors (m := CheckM) (fueledOps mode F)
            (consNestedFormers (stored.take p.k) env) (restoreTbl p st) p.lps a.ctors)
        = .ok ctorsR ∧
      -- the restored recursor types
      restoreRecTys (m := CheckM) (fueledOps mode F)
          (consNestedCtors ctorsR.flatten
            (consNestedFormers (stored.take p.k) env))
          (restoreTbl p st) p.lps
          ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
          (stored.take p.k) = .ok cvRms ∧
      restoreRecTys (m := CheckM) (fueledOps mode F)
          (consNestedCtors ctorsR.flatten
            (consNestedFormers (stored.take p.k) env))
          (restoreTbl p st) p.lps
          ((List.range p.numNested).map p.mimicRecName)
          (stored.drop p.k) = .ok cvRns ∧
      -- THE RESTORED RECURSORS' NAMES ARE PAIRWISE DISTINCT (K.39)
      certOnly mode (decide ((cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)) = true ∧
      -- THE AUXILIARY NAMES AND THE RESTORED RECURSORS' ARE DISJOINT
      -- (K.45): `RestoreAgree.auxFresh` at the provisioned environment
      certOnly mode ((restoreTbl p st).auxNames.all fun n =>
        !((cvRms.map (·.name) ++ cvRns.map (·.name)).contains n)) = true ∧
      -- the restored rules, at the rule-less provision
      (cvRms.zip (stored.take p.k)).mapM (fun (cvRa, a) =>
          restoreRules (m := CheckM) (fueledOps mode F)
            (provisionNestedRecs
              ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
                ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
              (consNestedCtors ctorsR.flatten
                (consNestedFormers (stored.take p.k) env)))
            (restoreTbl p st) cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules)
        = .ok rulesM ∧
      (cvRns.zip (stored.drop p.k)).mapM (fun (cvRa, a) =>
          restoreRules (m := CheckM) (fueledOps mode F)
            (provisionNestedRecs
              ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
                ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
              (consNestedCtors ctorsR.flatten
                (consNestedFormers (stored.take p.k) env)))
            (restoreTbl p st) cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules)
        = .ok rulesN ∧
      -- THE RESTORED RULES' RESCUE BITS (K.50): a set bit IS the
      -- provisioned environment's own verdict — `hctorStored`'s other
      -- two conjuncts, which `restoreRules` cannot transport
      certOnly mode (nestedRuleBitsOk
        (provisionNestedRecs
            ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
            (consNestedCtors ctorsR.flatten
              (consNestedFormers (stored.take p.k) env))).find?
        (cvRms.zip rulesM ++ cvRns.zip rulesN)) = true ∧
      -- the projection tables, on the stored recursors
      nestedTables (m := CheckM)
          (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
            ((p.formers.getD mIdx default).1.name, a.tbl, cs))
          (storeNestedRecs
            ((cvRms.zip ((stored.take p.k).zip rulesM)).map
                (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
              ++ (cvRns.zip ((stored.drop p.k).zip rulesN)).map
                (fun (cv, a, rs) => (cv, a.mI, a.rP, rs)))
            (consNestedCtors ctorsR.flatten
              (consNestedFormers (stored.take p.k) env))) = .ok envOut ∧
      -- POST-CHECK (a): the same pins at the RESTORED environment
      nestedPinsOk (m := CheckM) (fueledOps mode F) envOut p.nP st.pins = .ok () ∧
      -- **THE RECORDS' ARGUMENT SUMS ARE THE INSTALL'S** (K.54): the
      -- stored `(mI, rP)` per recursor IS the stream record's, so the
      -- cached mirror's skeleton is a function of the block the driver
      -- was handed rather than of the elimination's output
      (p.memberRecNums == ((stored.take p.k).map fun a => (a.mI, a.rP)) &&
        p.mimicRecNums == ((stored.drop p.k).map fun a => (a.mI, a.rP))) = true ∧
      -- POST-CHECK (c): the stream's records against the generated ones
      (p.memberRecs.length == cvRms.length && p.mimicRecs.length == cvRns.length) = true ∧
      nestedRecsOk (m := CheckM) (fueledOps mode F)
          (consNestedCtors ctorsR.flatten
            (consNestedFormers (stored.take p.k) env))
          p.nP b.k b.n
          ((((p.memberRecs.zip cvRms).zip rulesM).zipIdx.map
              (fun (((sr, cv), rs), mIdx) =>
                (sr, (b.ownCtors mIdx).map (fun (J, c) => (J, c.nF)), cv, rs)))
            ++ (((p.mimicRecs.zip cvRns).zip rulesN).zipIdx.map
              (fun (((sr, cv), rs), j) =>
                (sr, (b.ownCtors (p.k + j)).map (fun (J, c) => (J, c.nF)), cv, rs))))
        = .ok () ∧
      -- THE READ-BACK (K.34): `containerInfo?` of the environment this
      -- route produced, at every member, is the block's own data
      certOnly mode (blockReadBackOk envOut p.nP
        (((stored.take p.k).zip ctorsR).map fun (a, cs) =>
          (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))) = true ∧
      -- THE MIMICS' STORED TYPES ARE THE RECORDED PINS (K.47): the
      -- own-pin reader at the block's own levels and parameter openers
      -- returns the recorded pin list verbatim
      certOnly mode (nestedOwnPinsOk envOut p st) = true ∧
      -- THE OWN-PIN TABLE IS THE ROUTE'S OWN (K.43): the mimic recursors
      -- this route stored are exactly `T₁.rec_1 … T₁.rec_numNested`
      certOnly mode
        (blockOwnMimicsOk envOut (p.formers.headD default).1.name p.numNested) = true := by
  unfold checkNestedRest at h
  simp only at h
  obtain ⟨stored, hst, h⟩ := exceptBind_ok h
  have hst' := unwrapOr_ok hst
  try simp only at h
  by_cases hpc : pinsClosed p.nP st.pins = true
  case neg => rw [if_neg hpc] at h; close_throw
  rw [if_pos hpc] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨uA, hpinsAux, h⟩ := exceptBind_ok h
  try simp only at h
  by_cases hcaps : (stored.take p.k).all
      (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true
  case neg => rw [if_neg hcaps] at h; close_throw
  rw [if_pos hcaps] at h
  try simp only [bind, Except.bind] at h
  by_cases hsrc : certOnly (fueledOps mode F).mode (nestedCopySrcOk env p st) = true
  case neg => rw [if_neg hsrc] at h; close_throw
  rw [if_pos hsrc] at h
  try simp only [bind, Except.bind] at h
  by_cases hgrp : certOnly (fueledOps mode F).mode (nestedGroupsOk env p st) = true
  case neg => rw [if_neg hgrp] at h; close_throw
  rw [if_pos hgrp] at h
  try simp only [bind, Except.bind] at h
  by_cases hmn : certOnly (fueledOps mode F).mode (nestedPinMentionOk p st) = true
  case neg => rw [if_neg hmn] at h; close_throw
  rw [if_pos hmn] at h
  try simp only [bind, Except.bind] at h
  by_cases hsc : certOnly (fueledOps mode F).mode (pinsScoped p.nP st) = true
  case neg => rw [if_neg hsc] at h; close_throw
  rw [if_pos hsc] at h
  try simp only [bind, Except.bind] at h
  by_cases hpl : certOnly (fueledOps mode F).mode (pinsLevelsOk p.lps st.pins) = true
  case neg => rw [if_neg hpl] at h; close_throw
  rw [if_pos hpl] at h
  try simp only [bind, Except.bind] at h
  by_cases haa : certOnly (fueledOps mode F).mode (nestedAuxAppsOk p st stored) = true
  case neg => rw [if_neg haa] at h; close_throw
  rw [if_pos haa] at h
  try simp only [bind, Except.bind] at h
  by_cases hpa : certOnly (fueledOps mode F).mode (nestedPinParentOk p st) = true
  case neg => rw [if_neg hpa] at h; close_throw
  rw [if_pos hpa] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨uPC, hpc4, h⟩ := exceptBind_ok h
  obtain ⟨htg, hkd, hrk, hrh, hordC, hord, hpinN, hcpf, hcrf, him, hout, htgt, hstgt⟩ :=
    nestedPinChecks_inv hpc4
  try simp only at h
  obtain ⟨uP₁, hpins₁, h⟩ := exceptBind_ok h
  try simp only at h
  try simp only [bind, Except.bind] at h
  by_cases hres : pinsResolve (consNestedFormers (stored.take p.k) env) st.pins = true
  case neg => rw [if_neg hres] at h; close_throw
  rw [if_pos hres] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨ctorsR, hctors, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨cvRms, hrm, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨cvRns, hrn, h⟩ := exceptBind_ok h
  try simp only at h
  try simp only [bind, Except.bind] at h
  by_cases hnd : certOnly (fueledOps mode F).mode
      (decide ((cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)) = true
  case neg => rw [if_neg hnd] at h; close_throw
  rw [if_pos hnd] at h
  try simp only [bind, Except.bind] at h
  by_cases hdj : certOnly (fueledOps mode F).mode
      ((restoreTbl p st).auxNames.all fun n =>
        !((cvRms.map (·.name) ++ cvRns.map (·.name)).contains n)) = true
  case neg => rw [if_neg hdj] at h; close_throw
  rw [if_pos hdj] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨rulesM, hrlm, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨rulesN, hrln, h⟩ := exceptBind_ok h
  try simp only at h
  by_cases hrb2 : certOnly (fueledOps mode F).mode (nestedRuleBitsOk
      (provisionNestedRecs
            ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
            (consNestedCtors ctorsR.flatten
              (consNestedFormers (stored.take p.k) env))).find?
      (cvRms.zip rulesM ++ cvRns.zip rulesN)) = true
  case neg => rw [if_neg hrb2] at h; close_throw
  rw [if_pos hrb2] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨env₄, htbl, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨u₀, hpins, h⟩ := exceptBind_ok h
  try simp only at h
  by_cases hnums : (p.memberRecNums == ((stored.take p.k).map fun a => (a.mI, a.rP)) &&
      p.mimicRecNums == ((stored.drop p.k).map fun a => (a.mI, a.rP))) = true
  case neg => rw [if_neg hnums] at h; close_throw
  rw [if_pos hnums] at h
  try simp only [bind, Except.bind] at h
  by_cases hlen : (p.memberRecs.length == cvRms.length &&
      p.mimicRecs.length == cvRns.length) = true
  case neg => rw [if_neg hlen] at h; close_throw
  rw [if_pos hlen] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨u₁, hrecs, h⟩ := exceptBind_ok h
  try simp only at h
  by_cases hrb : certOnly (fueledOps mode F).mode
      (blockReadBackOk env₄ p.nP (((stored.take p.k).zip ctorsR).map fun (a, cs) =>
        (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))) = true
  case neg => rw [if_neg hrb] at h; close_throw
  rw [if_pos hrb] at h
  try simp only [bind, Except.bind] at h
  by_cases hop : certOnly (fueledOps mode F).mode (nestedOwnPinsOk env₄ p st) = true
  case neg => rw [if_neg hop] at h; close_throw
  rw [if_pos hop] at h
  try simp only [bind, Except.bind] at h
  by_cases hom : certOnly (fueledOps mode F).mode
      (blockOwnMimicsOk env₄ (p.formers.headD default).1.name p.numNested) = true
  case neg => rw [if_neg hom] at h; close_throw
  rw [if_pos hom] at h
  have henv : env₄ = envOut := by
    simpa [pure, Except.pure] using h
  subst henv
  exact ⟨stored, ctorsR, cvRms, cvRns, rulesM, rulesN,
    hst', hpc, (by cases uA; exact hpinsAux), hcaps, hsrc,
    certOnly_and_left hcont, hgrp, hmn, hsc, hpl, htg, hkd, haa, hrk, hpa, hrh, hordC,
    hord, hpinN, hcpf, hcrf, him, hout, htgt, hstgt, (by cases uP₁; exact hpins₁), hres, hctors,
    hrm, hrn,
    hnd, hdj,
    hrlm, hrln, hrb2, htbl, (by cases u₀; exact hpins), hnums, hlen,
    (by cases u₁; exact hrecs), hrb, hop, hom⟩

/-- **The whole nested chain**, as the install ran it. -/
theorem checkNested_inv {env envOut : Env} {p : NestedParts} {F : Nat}
    (h : checkNested (m := CheckM) (fueledOps mode F) env p = .ok envOut) :
    (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all
        (fun t => !t.mentionsNestedAux)) = true ∧
    uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true ∧
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env) (stored : List AuxStored)
      (ctorsR : List (List (ConstantVal × Nat × Nat)))
      (cvRms cvRns : List ConstantVal)
      (rulesM rulesN : List (List RecRule))
      (fmsA ctorsA : List ConstantVal),
      -- THE INPUTS, ANNOTATED (K.12): the formers as the install will
      -- store them, the constructors at the environment holding those
      -- formers — so every piece the elimination builds a copy out of is
      -- annotated, and no annotation pass is left to run on a copy
      nestedAnnotFormers (m := CheckM) (fueledOps mode F) env p.nP p.formers = .ok fmsA ∧
      nestedAnnotCtors (m := CheckM) (fueledOps mode F) (nestedFormerEnv fmsA env) p.ctors
        = .ok ctorsA ∧
      -- the elimination on those, and the mimic count against the
      -- stream's records
      elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA) = .ok st ∧
      st.pins.length = p.numNested ∧
      -- every MINTED name is free in the pre-block environment
      copiesFresh env p.k st = true ∧
      -- the CONTAINERS' facts (K.14): uniform occurrences of the group in
      -- the stored constructors, and the two recursor facts at every member
      certOnly mode (nestedContainersOk env st.pins) = true ∧
      -- **THE PINS' COMPONENTS REWRITE** (lane L-E's request): every
      -- component of every pin's argument spine goes through the
      -- elimination's own `replaceAllNested` at the final state.
      -- UNCONDITIONAL: the model's `recF`, `es` and `ordF`-left arms
      -- read the rewritten components in every mode
      nestedPinCompsOk env p st = true ∧
      -- the auxiliary mutual block, checked in a SCRATCH environment
      auxBlock p st = some b ∧
      checkMutualCore (m := CheckM) (fueledOps mode F) env b none true = .ok envAux ∧
      auxStoredAll envAux b b.k = some stored ∧
      -- `pinsClosed`: every pin, abstracted over the parameters, is
      -- fvar-free with its loose bvars inside the telescope
      pinsClosed p.nP st.pins = true ∧
      -- `pinsOkAux`: the pins — the elimination's own, annotated terms
      -- opened at the block's parameter variables — typed at the SCRATCH
      -- environment
      nestedPinsOk (m := CheckM) (fueledOps mode F) envAux p.nP st.pins = .ok () ∧
      -- the restored formers are fresh and carry no η bit (K.20)
      (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone)
        = true ∧
      -- THE COPIES' SOURCES (K.28): every minted auxiliary type is
      -- `mkCopy`'s output at the `(J, lvls, Ds)` it records, so the
      -- copy-instantiation identities are a field read
      certOnly mode (nestedCopySrcOk env p st) = true ∧
      -- THE PINS ARE STRUCTURALLY DISTINCT (K.15 (2), named at K.31):
      -- read off `nestedContainersOk`'s first conjunct, so this costs no
      -- second check — what `replaceAllNested`'s `find?` rewrite needs
      certOnly mode (pinsDistinct st.pins) = true ∧
      -- THE PINS' MINT GROUPS (K.29): the segment, its size, the
      -- member order, and the group's shared `lvls`/`Ds`
      certOnly mode (nestedGroupsOk env p st) = true ∧
      -- A PIN'S COMPONENTS MENTION A MEMBER (K.44): lane L-E's
      -- `nestMention`, whose witness the elimination's record does not pin
      certOnly mode (nestedPinMentionOk p st) = true ∧
      -- THE PINS' SCOPE (K.30): the pins' free variables are the first
      -- former's openers, annotation included, and no loose bvar
      certOnly mode (pinsScoped p.nP st) = true ∧
      -- THE PINS' LEVELS (K.48): every level parameter a pin mentions is
      -- the block's own — `ContainerModeled.pinParams` at the nested site
      certOnly mode (pinsLevelsOk p.lps st.pins) = true ∧
      -- THE COPIES' RECURSIVE TARGETS (K.32): a group-recursive copy
      -- field comes from the container's own recursion at the spine
      certOnly mode (nestedCopyTargetsOk env p b st stored) = true ∧
      -- THE FIELD KINDS (K.26): the auxiliary block's stored fields are
      -- classified `.ordinary`, `.recursive` or `.reflexive`, and
      -- `nestedPinKinds p b stored` is that classification
      certOnly mode (nestedPinKindsOk p b st stored) = true ∧
      -- THE AUXILIARY APPLICATIONS (K.35): the restore's
      -- `args.drop nP` precondition, at the read-back recursor types
      -- and rules
      certOnly mode (nestedAuxAppsOk p st stored) = true ∧
      -- THE PINS' CONTAINER INSTANCES AND RANK (K.37): the model's
      -- induction measure for step (iii)
      certOnly mode (nestedPinRankOk env p b st stored) = true ∧
      -- THE MINT PARENTS (K.40)
      certOnly mode (nestedPinParentOk p st) = true ∧
      -- THE PIN PAIRING AT A NOT-OWN EDGE (K.41): all four of `ClassPin`'s
      certOnly mode (nestedPinRootPairOk env p b st stored) = true ∧
      -- THE NOT-OWN REFERENCES' ORDER (K.57): a reference that leaves the
      -- instance goes to a container declared strictly earlier — the
      -- model's step (iii) inducts on it at a constant-headed field
      certOnly mode (nestedPinOrderOk env p b st stored) = true ∧
      -- THE POSITIVITY NORMALISATION ON THE MINTED COPY (K.42): at every
      -- ORDINARY field of every copy's constructor, the stored domain IS
      -- the normalisation of the MINTED one — lane L-B's `ordF`-left arm
      (mode.verifiedChecks = true →
        ∃ (jobs : List (Nat × Expr × Expr)) (ws : List Expr),
          nestedOrdDomPairs env p st stored (nestedPinKinds p b stored) = some jobs ∧
          nestedOrdNorms (m := CheckM) (fueledOps mode F)
              (consNestedFormers (stored.take p.k) env) b.memberNames jobs = .ok ws ∧
          ws = jobs.map (·.2.2)) ∧
      -- THE SAME WALK AT A PIN TARGET, REWRITTEN (K.51): there the
      -- stored domain is headed by the MIMIC and the minted one by the
      -- CONTAINER, so the normalisation's output is rewritten — by the
      -- elimination's own `replaceAllNested`, at the FINAL state, which
      -- therefore mints nothing — before the comparison
      (mode.verifiedChecks = true →
        ∃ (params : List Expr) (pbs₀ : List (Expr × BinderMeta))
          (jobsP : List (Nat × Expr × Expr)) (wsP : List Expr),
          nestedRewriteData p st = some (params, pbs₀) ∧
          nestedPinDomPairs env p st stored (nestedPinKinds p b stored) = some jobsP ∧
          nestedPinNorms (m := CheckM) (fueledOps mode F)
              (consNestedFormers (stored.take p.k) env) b.memberNames jobsP = .ok wsP ∧
          nestedPinRewrites env p st params pbs₀ jobsP wsP = true) ∧
      -- **A CONTAINER'S NESTED FIELD LANDS ON A BLOCK PIN** (K.60):
      -- at a container field headed by another stored container whose
      -- parameter part carries one of the container's own members, the
      -- copy's corresponding field is classified `.recursive` into a
      -- PIN.  K.32's twin, running the other way; UNCONDITIONAL, since
      -- the model's `pinF` arm reads it in every mode
      nestedCopyPinFieldsOk env p b st stored = true ∧
      -- **A CONTAINER'S REFLEXIVE NESTED FIELD LANDS ON A BLOCK PIN**
      -- (K.63): K.60's guard one `Π`-tower down, where K.60 claims
      -- nothing by construction; the same walk computes both
      nestedCopyReflFieldsOk env p b st stored = true ∧
      -- **THE CONTAINER INSTANCE MAP** (K.61): every own pin of every
      -- pin's container, instantiated at that pin's own levels and
      -- components, IS a block pin, and a copy's field at one of those
      -- own pins records the map's value as its target.  K.41's
      -- converse, and a FUNCTION where K.41 has only a covering
      nestedInstMapOk env p b st stored = true ∧
      -- **A REWRITTEN ORDINARY FIELD LEAVES THE INSTANCE** (K.62): at
      -- an `ordF`-right edge the recorded target is outside the
      -- instance map's image
      nestedOrdOutsideOk env p b st stored = true ∧
      -- **AND IT IS THE OWNING CONTAINER'S OWN CLASS, IMAGED** (K.67):
      -- K.62's positive twin at the same guard, recomputed from the
      -- container's stored constructor at the owner's own components
      nestedOrdTargetOk env p b st stored = true ∧
      -- **K.68**: and it is THIS block's own class, by its own
      -- recomputation
      nestedOrdSelfTargetOk env p b st stored = true ∧
      -- POST-CHECK (a) A THIRD TIME (K.30): the pins typed at the
      -- environment holding the RESTORED formers
      nestedPinsOk (m := CheckM) (fueledOps mode F)
          (consNestedFormers (stored.take p.k) env) p.nP st.pins = .ok () ∧
      -- **THE PINS' CONSTANTS RESOLVE** (K.64): at that same
      -- environment.  UNCONDITIONAL: the consumer — a container's
      -- pins' components' READINGS, which cross a later install only
      -- under the projection guard — reads it in every mode
      pinsResolve (consNestedFormers (stored.take p.k) env) st.pins = true ∧
      -- the restored constructors, at the environment holding the formers
      (stored.take p.k).mapM (fun a =>
          restoreCtors (m := CheckM) (fueledOps mode F)
            (consNestedFormers (stored.take p.k) env) (restoreTbl p st) p.lps a.ctors)
        = .ok ctorsR ∧
      -- the restored recursor types
      restoreRecTys (m := CheckM) (fueledOps mode F)
          (consNestedCtors ctorsR.flatten
            (consNestedFormers (stored.take p.k) env))
          (restoreTbl p st) p.lps
          ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
          (stored.take p.k) = .ok cvRms ∧
      restoreRecTys (m := CheckM) (fueledOps mode F)
          (consNestedCtors ctorsR.flatten
            (consNestedFormers (stored.take p.k) env))
          (restoreTbl p st) p.lps
          ((List.range p.numNested).map p.mimicRecName)
          (stored.drop p.k) = .ok cvRns ∧
      -- THE RESTORED RECURSORS' NAMES ARE PAIRWISE DISTINCT (K.39)
      certOnly mode (decide ((cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)) = true ∧
      -- THE AUXILIARY NAMES AND THE RESTORED RECURSORS' ARE DISJOINT
      -- (K.45): `RestoreAgree.auxFresh` at the provisioned environment
      certOnly mode ((restoreTbl p st).auxNames.all fun n =>
        !((cvRms.map (·.name) ++ cvRns.map (·.name)).contains n)) = true ∧
      -- the restored rules, at the rule-less provision
      (cvRms.zip (stored.take p.k)).mapM (fun (cvRa, a) =>
          restoreRules (m := CheckM) (fueledOps mode F)
            (provisionNestedRecs
              ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
                ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
              (consNestedCtors ctorsR.flatten
                (consNestedFormers (stored.take p.k) env)))
            (restoreTbl p st) cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules)
        = .ok rulesM ∧
      (cvRns.zip (stored.drop p.k)).mapM (fun (cvRa, a) =>
          restoreRules (m := CheckM) (fueledOps mode F)
            (provisionNestedRecs
              ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
                ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
              (consNestedCtors ctorsR.flatten
                (consNestedFormers (stored.take p.k) env)))
            (restoreTbl p st) cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules)
        = .ok rulesN ∧
      -- THE RESTORED RULES' RESCUE BITS (K.50): a set bit IS the
      -- provisioned environment's own verdict — `hctorStored`'s other
      -- two conjuncts, which `restoreRules` cannot transport
      certOnly mode (nestedRuleBitsOk
        (provisionNestedRecs
            ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
            (consNestedCtors ctorsR.flatten
              (consNestedFormers (stored.take p.k) env))).find?
        (cvRms.zip rulesM ++ cvRns.zip rulesN)) = true ∧
      -- the projection tables, on the stored recursors
      nestedTables (m := CheckM)
          (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
            ((p.formers.getD mIdx default).1.name, a.tbl, cs))
          (storeNestedRecs
            ((cvRms.zip ((stored.take p.k).zip rulesM)).map
                (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
              ++ (cvRns.zip ((stored.drop p.k).zip rulesN)).map
                (fun (cv, a, rs) => (cv, a.mI, a.rP, rs)))
            (consNestedCtors ctorsR.flatten
              (consNestedFormers (stored.take p.k) env))) = .ok envOut ∧
      -- POST-CHECK (a): the same pins at the RESTORED environment
      nestedPinsOk (m := CheckM) (fueledOps mode F) envOut p.nP st.pins = .ok () ∧
      -- **THE RECORDS' ARGUMENT SUMS ARE THE INSTALL'S** (K.54): the
      -- stored `(mI, rP)` per recursor IS the stream record's, so the
      -- cached mirror's skeleton is a function of the block the driver
      -- was handed rather than of the elimination's output
      (p.memberRecNums == ((stored.take p.k).map fun a => (a.mI, a.rP)) &&
        p.mimicRecNums == ((stored.drop p.k).map fun a => (a.mI, a.rP))) = true ∧
      -- POST-CHECK (c): the stream's records against the generated ones
      (p.memberRecs.length == cvRms.length && p.mimicRecs.length == cvRns.length) = true ∧
      nestedRecsOk (m := CheckM) (fueledOps mode F)
          (consNestedCtors ctorsR.flatten
            (consNestedFormers (stored.take p.k) env))
          p.nP b.k b.n
          ((((p.memberRecs.zip cvRms).zip rulesM).zipIdx.map
              (fun (((sr, cv), rs), mIdx) =>
                (sr, (b.ownCtors mIdx).map (fun (J, c) => (J, c.nF)), cv, rs)))
            ++ (((p.mimicRecs.zip cvRns).zip rulesN).zipIdx.map
              (fun (((sr, cv), rs), j) =>
                (sr, (b.ownCtors (p.k + j)).map (fun (J, c) => (J, c.nF)), cv, rs))))
        = .ok () ∧
      -- THE READ-BACK (K.34): `containerInfo?` of the environment this
      -- route produced, at every member, is the block's own data
      certOnly mode (blockReadBackOk envOut p.nP
        (((stored.take p.k).zip ctorsR).map fun (a, cs) =>
          (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))) = true ∧
      -- THE MIMICS' STORED TYPES ARE THE RECORDED PINS (K.47): the
      -- own-pin reader at the block's own levels and parameter openers
      -- returns the recorded pin list verbatim
      certOnly mode (nestedOwnPinsOk envOut p st) = true ∧
      -- THE OWN-PIN TABLE IS THE ROUTE'S OWN (K.43): the mimic recursors
      -- this route stored are exactly `T₁.rec_1 … T₁.rec_numNested`
      certOnly mode
        (blockOwnMimicsOk envOut (p.formers.headD default).1.name p.numNested) = true := by
  obtain ⟨hg₀, hg₁, st, b, envAux, fmsA, ctorsA, hfmsA, hctorsA, helim, hcnt, hfresh,
    hcont, hcomp, hb, haux, hrest⟩ := checkNested_inv_front h
  obtain ⟨stored, ctorsR, cvRms, cvRns, rulesM, rulesN, hst, hpc, hpinsAux, hcaps, hsrc,
    hdist, hgrp, hmn, hsc, hpl, htg, hkd, haa, hrk, hpa, hrh, hordC, hord, hpinN, hcpf,
    hcrf, him, hout, htgt, hstgt, hpins₁, hctors, hrm, hrn, hnd, hdj, hrlm, hrln, hrb2, htbl, hpins,
    hnums, hlen, hrecs, hrb, hop, hom⟩ := checkNested_inv_rest hcont hrest
  exact ⟨hg₀, hg₁, st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, fmsA,
    ctorsA, hfmsA, hctorsA, helim, hcnt, hfresh, hcont, hcomp, hb, haux, hst, hpc,
    hpinsAux, hcaps, hsrc, hdist, hgrp, hmn, hsc, hpl, htg, hkd, haa, hrk, hpa, hrh,
    hordC, hord, hpinN, hcpf, hcrf, him, hout, htgt, hstgt, hpins₁, hctors, hrm, hrn, hnd, hdj, hrlm,
    hrln, hrb2, htbl, hpins, hnums, hlen, hrecs, hrb, hop, hom⟩


/-! ## The restore, syntactically (task #315)

`restore_nested`'s replace (`ConLeche/Kernel/Inductives/NestedInstall.lean`)
read as a syntactic walk: the prune, the node step's verdict at each shape
of node, the Π node both ways, a pin's fire, the telescope prologue and the
rebuild — and the commutation with opening a binder, which is what a reader
that descends a restored telescope one binder at a time needs. -/

/-- An application spine mentions its head constant. -/
theorem Expr.mentionsConst_of_getAppFn {n : Name} : ∀ {e : Expr} {us : List Level},
    e.getAppFn = .const n us → e.mentionsConst n = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro us h
    simp only [Expr.mentionsConst, ihf (by simpa only [Expr.getAppFn] using h), Bool.true_or]
  | const m vs =>
    intro us h
    simp only [Expr.getAppFn, Expr.const.injEq] at h
    simp [Expr.mentionsConst, h.1]
  | _ => intro us h; simp [Expr.getAppFn] at h

/-- Instantiation does not move a constant head. -/
theorem Expr.getAppFn_instantiate1_const {v : Expr} {n : Name} {us : List Level} :
    ∀ {e : Expr} {j : Nat}, e.getAppFn = .const n us →
      (e.instantiate1 v j).getAppFn = .const n us := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro j h
    simp only [Expr.instantiate1, Expr.getAppFn]
    exact ihf (by simpa only [Expr.getAppFn] using h)
  | const m vs => intro j h; simpa only [Expr.instantiate1] using h
  | _ => intro j h; simp [Expr.getAppFn] at h

/-- ... and a constant head after instantiating a VARIABLE was one
before: `instantiate1` puts an `fvar` — never a constant — where the
`bvar` stood. -/
theorem Expr.getAppFn_const_of_instantiate1 {k : Nat} {tyv : Expr} {n : Name} {us : List Level} :
    ∀ {e : Expr} {j : Nat}, (e.instantiate1 (.fvar k tyv) j).getAppFn = .const n us →
      e.getAppFn = .const n us := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro j h
    simp only [Expr.getAppFn]
    exact ihf (by simpa only [Expr.instantiate1, Expr.getAppFn] using h)
  | bvar i =>
    intro j h
    simp only [Expr.instantiate1] at h
    split at h
    · simp [Expr.getAppFn] at h
    · split at h <;> simp [Expr.getAppFn] at h
  | const m vs => intro j h; simpa only [Expr.instantiate1] using h
  | _ => intro j h; simp [Expr.instantiate1, Expr.getAppFn] at h

/-- Instantiating a variable maps the spine's arguments; in particular
the argument count is unchanged, which is what the node step's
`args.length < R.nP` guard reads. -/
theorem Expr.getAppArgs_instantiate1_var {k : Nat} {tyv : Expr} :
    ∀ {e : Expr} {j : Nat}, (e.instantiate1 (.fvar k tyv) j).getAppArgs
      = e.getAppArgs.map (fun a => a.instantiate1 (.fvar k tyv) j) := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro j
    simp only [Expr.instantiate1, Expr.getAppArgs, ihf, List.map_append, List.map_cons,
      List.map_nil]
  | bvar i =>
    intro j
    simp only [Expr.instantiate1]
    split
    · simp [Expr.getAppArgs]
    · split <;> simp [Expr.getAppArgs]
  | _ => intro j; simp [Expr.instantiate1, Expr.getAppArgs]

/-- A constant mentioned before a substitution is mentioned after it:
`instantiate1` only replaces `bvar`s and keeps every other node. -/
theorem Expr.mentionsConst_instantiate1 {v : Expr} {m : Name} :
    ∀ {e : Expr} {j : Nat}, e.mentionsConst m = true →
      (e.instantiate1 v j).mentionsConst m = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro j h
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h ⊢
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true]
    exact h.imp (fun h1 => ihf h1) (fun h2 => iha h2)
  | lam ty b bm ihty ihb =>
    intro j h
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true]
    exact h.imp (fun h1 => ihty h1) (fun h2 => ihb h2)
  | forallE ty b bm ihty ihb =>
    intro j h
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true]
    exact h.imp (fun h1 => ihty h1) (fun h2 => ihb h2)
  | letE ty vl b ihty ihv ihb =>
    intro j h
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true]
    exact h.imp (fun h1 => h1.imp (fun h2 => ihty h2) (fun h2 => ihv h2)) (fun h2 => ihb h2)
  | proj s i pe ih =>
    intro j h
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h ⊢
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true]
    exact h.imp id (fun h2 => ih h2)
  | bvar i => intro j h; simp [Expr.mentionsConst] at h
  | _ => intro j h; simpa only [Expr.instantiate1] using h

/-! ### The prune, and the nodes the step declines at -/

/-- **The prune**: a term mentioning none of `R.auxNames` is its own
restoration. -/
theorem restoreWalk_of_no_aux {R : RestoreTbl} : ∀ (d : Nat) (e : Expr),
    (∀ n ∈ R.auxNames, e.mentionsConst n = false) → restoreWalk R d e = .ok e := by
  intro d e h
  have hp : (R.auxNames.any fun n => e.mentionsConst n) = false := by
    simp only [List.any_eq_false]
    intro n hn
    simp [h n hn]
  rw [restoreWalk.eq_def]
  simp only [hp, Bool.not_false, if_pos]

/-- **The node step declines at a Π** — a Π is not a `.const`, and the
head of a non-application is the node itself. -/
theorem restoreNode_forallE {R : RestoreTbl} {d : Nat} {ty b : Expr} {bm : BinderMeta} :
    restoreNode R d (.forallE ty b bm) = .ok none := rfl

/-- The node step declines at a λ. -/
theorem restoreNode_lam {R : RestoreTbl} {d : Nat} {ty b : Expr} {bm : BinderMeta} :
    restoreNode R d (.lam ty b bm) = .ok none := rfl

/-- The node step declines at an `fvar`. -/
theorem restoreNode_fvar {R : RestoreTbl} {d i : Nat} {ty : Expr} :
    restoreNode R d (.fvar i ty) = .ok none := rfl

/-- The node step declines at a `bvar`. -/
theorem restoreNode_bvar {R : RestoreTbl} {d i : Nat} :
    restoreNode R d (.bvar i) = .ok none := rfl

/-- The node step declines at a sort. -/
theorem restoreNode_sort {R : RestoreTbl} {d : Nat} {u : Level} :
    restoreNode R d (.sort u) = .ok none := rfl

/-- The prune's `any`, read as the per-name fact. -/
theorem auxNames_mention_false {R : RestoreTbl} {e : Expr}
    (hp : (R.auxNames.any fun n => e.mentionsConst n) = false) :
    ∀ n ∈ R.auxNames, e.mentionsConst n = false := by
  intro n hn
  have h1 := List.any_eq_false.mp hp n hn
  simpa using h1

/-- A Π mentions a constant exactly when one of its two parts does. -/
theorem Expr.mentionsConst_forallE_false {n : Name} {ty b : Expr} {bm : BinderMeta}
    (h : (Expr.forallE ty b bm).mentionsConst n = false) :
    ty.mentionsConst n = false ∧ b.mentionsConst n = false := by
  simpa only [Expr.mentionsConst, Bool.or_eq_false_iff] using h

/-! ### The Π node, both ways -/

/-- **The Π node, inverted**: the walk of a Π is the walk of its domain
and of its body one binder deeper — in the pruned case both are the
identity, by the prune on the two parts. -/
theorem restoreWalk_forallE_inv {R : RestoreTbl} {d : Nat} {ty b e' : Expr} {bm : BinderMeta}
    (h : restoreWalk R d (.forallE ty b bm) = .ok e') :
    ∃ ty' b', restoreWalk R d ty = .ok ty' ∧ restoreWalk R (d + 1) b = .ok b' ∧
      e' = .forallE ty' b' bm := by
  rcases Bool.eq_false_or_eq_true
      (R.auxNames.any fun n => (Expr.forallE ty b bm).mentionsConst n) with hp | hp
  · simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false,
      restoreNode_forallE] at h
    cases hty : restoreWalk R d ty with
    | error err => rw [hty] at h; simp at h
    | ok ty' =>
      rw [hty] at h
      cases hb : restoreWalk R (d + 1) b with
      | error err => rw [hb] at h; simp at h
      | ok b' =>
        rw [hb] at h
        exact ⟨ty', b', rfl, rfl, (Except.ok.inj h).symm⟩
  · simp only [restoreWalk, hp, Bool.not_false, if_pos] at h
    have hp' := fun n hn => Expr.mentionsConst_forallE_false (auxNames_mention_false hp n hn)
    exact ⟨ty, b, restoreWalk_of_no_aux _ _ (fun n hn => (hp' n hn).1),
      restoreWalk_of_no_aux _ _ (fun n hn => (hp' n hn).2), (Except.ok.inj h).symm⟩

/-- **The Π node, forward.** -/
theorem restoreWalk_forallE {R : RestoreTbl} {d : Nat} {ty b ty' b' : Expr} {bm : BinderMeta}
    (hty : restoreWalk R d ty = .ok ty') (hb : restoreWalk R (d + 1) b = .ok b') :
    restoreWalk R d (.forallE ty b bm) = .ok (.forallE ty' b' bm) := by
  rcases Bool.eq_false_or_eq_true
      (R.auxNames.any fun n => (Expr.forallE ty b bm).mentionsConst n) with hp | hp
  · simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false,
      restoreNode_forallE, hty, hb]
  · have hp' := fun n hn => Expr.mentionsConst_forallE_false (auxNames_mention_false hp n hn)
    rw [restoreWalk_of_no_aux d ty (fun n hn => (hp' n hn).1)] at hty
    rw [restoreWalk_of_no_aux (d + 1) b (fun n hn => (hp' n hn).2)] at hb
    obtain rfl := Except.ok.inj hty
    obtain rfl := Except.ok.inj hb
    simp only [restoreWalk, hp, Bool.not_false, if_pos]

/-! ### A pin's fire -/

/-- An application spine mentions whatever its head mentions. -/
theorem Expr.mentionsConst_mkAppN_head {m : Name} : ∀ (args : List Expr) (f : Expr),
    f.mentionsConst m = true → (Expr.mkAppN f args).mentionsConst m = true
  | [], _, h => h
  | a :: as, f, h =>
    Expr.mentionsConst_mkAppN_head as (.app f a) (by
      simp only [Expr.mentionsConst, h, Bool.true_or])

/-- **A pin's fire**: at `auxJ p⃗ is` with `auxJ` a pin key (and an
`auxNames` entry, so the prune does not fire) the walk replaces the node
by the lifted pin applied to the arguments past the parameters, and the
arguments are NOT visited.  `hrec` is what the bare-`.const` case needs:
at `args = []` the outer match consults `recMap` first. -/
theorem restoreWalk_pin {R : RestoreTbl} {d : Nat} {n : Name} {us : List Level}
    {args : List Expr} {pin : Expr}
    (hp : R.pins.lookup n = some pin) (hrec : R.recMap.lookup n = none)
    (haux : n ∈ R.auxNames) (hlen : R.nP ≤ args.length) :
    restoreWalk R d (Expr.mkAppN (.const n us) args) =
      .ok (Expr.mkAppN (pin.liftLooseBVars d 0) (args.drop R.nP)) := by
  have hment : (R.auxNames.any fun m =>
      (Expr.mkAppN (.const n us) args).mentionsConst m) = true := by
    simp only [List.any_eq_true]
    exact ⟨n, haux, Expr.mentionsConst_mkAppN_head args _ (by simp [Expr.mentionsConst])⟩
  have hnode : restoreNode R d (Expr.mkAppN (.const n us) args) =
      .ok (some (Expr.mkAppN (pin.liftLooseBVars d 0) (args.drop R.nP))) := by
    rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
    · have h0 : R.nP = 0 := Nat.le_zero.mp hlen
      simp only [Expr.mkAppN, restoreNode, hrec, hp, Expr.getAppFn, Expr.getAppArgs, h0]
      simp
    · rw [List.concat_eq_append, Expr.mkAppN_append_one]
      have hfn : (Expr.app (Expr.mkAppN (.const n us) as) a).getAppFn = .const n us := by
        show (Expr.mkAppN (.const n us) as).getAppFn = _
        rw [Expr.getAppFn_mkAppN]
        rfl
      have hargs : (Expr.app (Expr.mkAppN (.const n us) as) a).getAppArgs = as ++ [a] := by
        show (Expr.mkAppN (.const n us) as).getAppArgs ++ [a] = _
        rw [Expr.getAppArgs_mkAppN]
        rfl
      rw [List.concat_eq_append] at hlen
      simp only [restoreNode, hfn, hargs, hp, if_neg (Nat.not_lt.mpr hlen)]
  rw [restoreWalk.eq_def]
  simp only [hment, Bool.not_true, Bool.false_eq_true, if_false, hnode]

/-! ### The prologue and the rebuild -/

/-- **The prologue**: `stripPisOrLams` peels the Πs a `stripPis` peels. -/
theorem stripPisOrLams_of_stripPis {k : Nat} {e : Expr} {bs : List (Expr × BinderMeta)}
    {body : Expr} (h : e.stripPis k = some (bs, body)) :
    stripPisOrLams k e = some (bs, body) := by
  induction k generalizing e bs body with
  | zero => simpa only [Expr.stripPis, stripPisOrLams] using h
  | succ k ih =>
    cases e with
    | forallE ty b bm =>
      rw [Expr.stripPis] at h
      cases hb : b.stripPis k with
      | none => rw [hb] at h; simp at h
      | some q =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [stripPisOrLams, ih hb, Option.map_some]
    | _ => simp [Expr.stripPis] at h

/-- **The rebuild, for a type**: on a Π-prefix `restoreNested` walks the
body at depth 0 and puts the Πs back.  `hpi` is what decides the
rebuild's binder; at `R.nP = 0` the telescope is empty and the flag does
not matter. -/
theorem restoreNested_pis {R : RestoreTbl} {e e' : Expr} {bs : List (Expr × BinderMeta)}
    {body : Expr} (hs : e.stripPis R.nP = some (bs, body))
    (hpi : 0 < R.nP → ∃ ty b bm, e = .forallE ty b bm)
    (h : restoreNested R e = .ok e') :
    ∃ body', restoreWalk R 0 body = .ok body' ∧
      e' = bs.foldr (fun (b : Expr × BinderMeta) acc => Expr.forallE b.1 acc b.2) body' := by
  have hso := stripPisOrLams_of_stripPis hs
  simp only [restoreNested, hso] at h
  cases hw : restoreWalk R 0 body with
  | error err => rw [hw] at h; simp at h
  | ok body' =>
    rw [hw] at h
    refine ⟨body', rfl, ?_⟩
    cases hnP : R.nP with
    | zero =>
      rw [hnP] at hs
      simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simpa using h.symm
    | succ k =>
      obtain ⟨ty, b, bm, rfl⟩ := hpi (by omega)
      simpa using h.symm

/-! ### The node step's head half

`restoreNode`'s `let head` restated, so that the `.const`/other split is
made once; `restoreNode_eq_head` and `restoreNode_const` pin this copy to
the kernel's by `rfl`. -/

/-- The head half of `restoreNode`'s step (its `let head`), restated. -/
@[expose] def restoreHead (R : RestoreTbl) (d : Nat) (e : Expr) : Except CheckError (Option Expr) :=
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    match R.pins.lookup n with
    | some pin =>
      if args.length < R.nP then
        .error (.invalid "failed to restore nested inductive types, auxiliary type is \
          not applied to all parameters")
      else .ok (some (Expr.mkAppN (pin.liftLooseBVars d 0) (args.drop R.nP)))
    | none =>
      match R.ctorPins.find? (fun q => q.1 == n) with
      | some (_, pin, newName) =>
        if args.length < R.nP then
          .error (.invalid "failed to restore nested inductive types, auxiliary \
            constructor is not applied to all parameters")
        else
          let nested := pin.liftLooseBVars d 0
          match nested.getAppFn with
          | .const _ ilvls =>
            .ok (some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls) nested.getAppArgs)
              (args.drop R.nP)))
          | _ =>
            .error (.invalid "failed to restore nested inductive types, nested \
              occurrence is not an inductive type application")
      | none => .ok none
  | _ => .ok none

/-- Off a `.const` node, the step IS its head half. -/
theorem restoreNode_eq_head {R : RestoreTbl} {d : Nat} {e : Expr}
    (h : ∀ n us, e ≠ .const n us) : restoreNode R d e = restoreHead R d e := by
  cases e with
  | const n us => exact absurd rfl (h n us)
  | _ => rfl

/-- At a `.const` node the recursor map is consulted first. -/
theorem restoreNode_const {R : RestoreTbl} {d : Nat} {n : Name} {us : List Level} :
    restoreNode R d (.const n us) =
      match R.recMap.lookup n with
      | some n' => .ok (some (.const n' us))
      | none => restoreHead R d (.const n us) := by
  rfl

/-- The head half declines when the spine head is not a constant. -/
theorem restoreHead_not_const {R : RestoreTbl} {d : Nat} {e : Expr}
    (h : ∀ n us, e.getAppFn ≠ .const n us) : restoreHead R d e = .ok none := by
  unfold restoreHead
  split
  · next n us heq => exact absurd heq (h n us)
  · rfl

/-- **The head half commutes with opening a binder**: the spine head and
the argument count are untouched by `instantiate1` at an `fvar`, and a
fired pin loses exactly one lift level
(`Expr.instantiate1_liftLooseBVars`). -/
theorem restoreHead_inst {R : RestoreTbl} {k : Nat} {tyv : Expr} {d j : Nat} {e : Expr}
    {o : Option Expr} (h : restoreHead R (d + 1 + j) e = .ok o) :
    restoreHead R (d + j) (e.instantiate1 (.fvar k tyv) j) =
      .ok (o.map (fun x => x.instantiate1 (.fvar k tyv) j)) := by
  by_cases hc : ∃ n us, e.getAppFn = .const n us
  case neg =>
    have hne : ∀ n us, e.getAppFn ≠ .const n us := fun n us hq => hc ⟨n, us, hq⟩
    rw [restoreHead_not_const hne] at h
    obtain rfl := (Except.ok.inj h).symm
    rw [restoreHead_not_const
      (fun n us hq => hne n us (Expr.getAppFn_const_of_instantiate1 hq))]
    rfl
  case pos =>
    obtain ⟨n, us, hfn⟩ := hc
    have hfn' : (e.instantiate1 (.fvar k tyv) j).getAppFn = .const n us :=
      Expr.getAppFn_instantiate1_const hfn
    have hargs : (e.instantiate1 (.fvar k tyv) j).getAppArgs
        = e.getAppArgs.map (fun a => a.instantiate1 (.fvar k tyv) j) :=
      Expr.getAppArgs_instantiate1_var
    simp only [restoreHead, hfn] at h
    simp only [restoreHead, hfn', hargs, List.length_map]
    cases hp : R.pins.lookup n with
    | some pin =>
      simp only [hp] at h ⊢
      by_cases hlen : e.getAppArgs.length < R.nP
      · rw [if_pos hlen] at h; simp at h
      · rw [if_neg hlen] at h ⊢
        obtain rfl := (Except.ok.inj h).symm
        have hlift : (pin.liftLooseBVars (d + 1 + j) 0).instantiate1 (.fvar k tyv) j
            = pin.liftLooseBVars (d + j) 0 := by
          rw [show d + 1 + j = (d + j) + 1 from by omega]
          exact Expr.instantiate1_liftLooseBVars (Nat.zero_le _) (by omega)
        simp only [Option.map_some, Expr.mkAppN_instantiate1, hlift, List.map_drop]
    | none =>
      simp only [hp] at h ⊢
      cases hcp : R.ctorPins.find? (fun q => q.1 == n) with
      | none =>
        simp only [hcp] at h ⊢
        obtain rfl := Except.ok.inj h
        rfl
      | some q =>
        obtain ⟨cn, pin, newName⟩ := q
        simp only [hcp] at h ⊢
        by_cases hlen : e.getAppArgs.length < R.nP
        · rw [if_pos hlen] at h; simp at h
        · rw [if_neg hlen] at h ⊢
          have hlift : (pin.liftLooseBVars (d + 1 + j) 0).instantiate1 (.fvar k tyv) j
              = pin.liftLooseBVars (d + j) 0 := by
            rw [show d + 1 + j = (d + j) + 1 from by omega]
            exact Expr.instantiate1_liftLooseBVars (Nat.zero_le _) (by omega)
          cases hnf : (pin.liftLooseBVars (d + 1 + j) 0).getAppFn with
          | const n₀ ilvls =>
            have hgf : (pin.liftLooseBVars (d + j) 0).getAppFn = .const n₀ ilvls := by
              rw [← hlift]; exact Expr.getAppFn_instantiate1_const hnf
            have hga : (pin.liftLooseBVars (d + j) 0).getAppArgs
                = (pin.liftLooseBVars (d + 1 + j) 0).getAppArgs.map
                    (fun a => a.instantiate1 (.fvar k tyv) j) := by
              rw [← hlift]; exact Expr.getAppArgs_instantiate1_var
            simp only [hnf] at h
            simp only [hgf, hga]
            obtain rfl := (Except.ok.inj h).symm
            simp only [Option.map_some, Expr.mkAppN_instantiate1, Expr.instantiate1,
              List.map_drop]
          | _ => simp only [hnf] at h; simp at h


/-- The step declines at a node that is neither a constant nor
constant-headed. -/
theorem restoreNode_none_of_not_const {R : RestoreTbl} {d : Nat} {e : Expr}
    (h1 : ∀ n us, e ≠ .const n us) (h2 : ∀ n us, e.getAppFn ≠ .const n us) :
    restoreNode R d e = .ok none := by
  rw [restoreNode_eq_head h1, restoreHead_not_const h2]

/-- **The node step commutes with opening a binder.** -/
theorem restoreNode_inst {R : RestoreTbl} {k : Nat} {tyv : Expr} {d j : Nat} {e : Expr}
    {o : Option Expr} (h : restoreNode R (d + 1 + j) e = .ok o) :
    restoreNode R (d + j) (e.instantiate1 (.fvar k tyv) j) =
      .ok (o.map (fun x => x.instantiate1 (.fvar k tyv) j)) := by
  cases e with
  | const n us =>
    rw [restoreNode_const] at h
    simp only [Expr.instantiate1, restoreNode_const]
    cases hr : R.recMap.lookup n with
    | some n' =>
      rw [hr] at h
      simp only at h
      obtain rfl := Except.ok.inj h
      rfl
    | none =>
      rw [hr] at h
      simp only at h
      exact restoreHead_inst h
  | bvar i =>
    rw [restoreNode_bvar] at h
    obtain rfl := Except.ok.inj h
    simp only [Expr.instantiate1]
    split
    · exact restoreNode_fvar
    · split <;> exact restoreNode_bvar
  | app f a =>
    rw [restoreNode_eq_head (by intro n us hq; exact Expr.noConfusion hq)] at h
    rw [restoreNode_eq_head (by intro n us hq; simp [Expr.instantiate1] at hq)]
    exact restoreHead_inst h
  | _ =>
    rw [restoreNode_none_of_not_const (by intro n us hq; exact Expr.noConfusion hq)
      (by intro n us hq; simp [Expr.getAppFn] at hq)] at h
    obtain rfl := Except.ok.inj h
    simp only [Expr.instantiate1]
    exact restoreNode_none_of_not_const (by intro n us hq; exact Expr.noConfusion hq)
      (by intro n us hq; simp [Expr.getAppFn] at hq)


/-! ### The prune's side condition -/

/-- **The prune's side condition**: every name the node step can fire on
is an `auxNames` entry.  Without it the prune is not sound for the walk's
descent — a subterm mentioning only, say, a `ctorPins` key would be
dismissed — and the commutation below is refutable.  NOTE that
`restoreTbl` (`ConLeche/Kernel/Inductives/NestedInstall.lean`) fills
`auxNames` from the PINS alone, so this is a hypothesis about the table,
not a fact of the structure. -/
@[expose] def RestoreTbl.KeysInAux (R : RestoreTbl) : Prop :=
  (∀ n pin, R.pins.lookup n = some pin → n ∈ R.auxNames) ∧
  (∀ n q, R.ctorPins.find? (fun p => p.1 == n) = some q → n ∈ R.auxNames) ∧
  (∀ n n', R.recMap.lookup n = some n' → n ∈ R.auxNames)

/-- The head half declines when neither pin map answers at the head. -/
theorem restoreHead_none {R : RestoreTbl} {d : Nat} {e : Expr}
    (hpin : ∀ n us, e.getAppFn = .const n us → R.pins.lookup n = none)
    (hctor : ∀ n us, e.getAppFn = .const n us →
      R.ctorPins.find? (fun p => p.1 == n) = none) :
    restoreHead R d e = .ok none := by
  by_cases hc : ∃ n us, e.getAppFn = .const n us
  · obtain ⟨n, us, hfn⟩ := hc
    simp only [restoreHead, hfn, hpin n us hfn, hctor n us hfn]
  · exact restoreHead_not_const (fun n us hq => hc ⟨n, us, hq⟩)

/-- The step declines when no map answers at the head. -/
theorem restoreNode_none_of_head {R : RestoreTbl} {d : Nat} {e : Expr}
    (hpin : ∀ n us, e.getAppFn = .const n us → R.pins.lookup n = none)
    (hctor : ∀ n us, e.getAppFn = .const n us →
      R.ctorPins.find? (fun p => p.1 == n) = none)
    (hrec : ∀ n us, e = .const n us → R.recMap.lookup n = none) :
    restoreNode R d e = .ok none := by
  cases e with
  | const n us =>
    simp only [restoreNode_const, hrec n us rfl]
    exact restoreHead_none hpin hctor
  | _ =>
    rw [restoreNode_eq_head (by intro n us hq; exact Expr.noConfusion hq)]
    exact restoreHead_none hpin hctor

/-- The step declines at any node whose spine head is the spine head of
an auxiliary-free term — in particular at that term and at its opening
`e₀.instantiate1 (.fvar k ty) j`, whose `fvar` annotation may well mention
an auxiliary name. -/
theorem restoreNode_none_of_aux_free {R : RestoreTbl} (hk : R.KeysInAux) {d : Nat} {e₀ e : Expr}
    (hfree : ∀ n ∈ R.auxNames, e₀.mentionsConst n = false)
    (hhead : ∀ n us, e.getAppFn = .const n us → e₀.getAppFn = .const n us) :
    restoreNode R d e = .ok none := by
  have key : ∀ n us, e.getAppFn = .const n us → n ∉ R.auxNames := by
    intro n us hq hn
    have h1 : e₀.mentionsConst n = true := Expr.mentionsConst_of_getAppFn (hhead n us hq)
    rw [hfree n hn] at h1
    exact Bool.noConfusion h1
  refine restoreNode_none_of_head ?_ ?_ ?_
  · intro n us hq
    cases hl : R.pins.lookup n with
    | none => rfl
    | some pin => exact absurd (hk.1 n pin hl) (key n us hq)
  · intro n us hq
    cases hl : R.ctorPins.find? (fun p => p.1 == n) with
    | none => rfl
    | some q => exact absurd (hk.2.1 n q hl) (key n us hq)
  · intro n us hq
    cases hl : R.recMap.lookup n with
    | none => rfl
    | some n' => exact absurd (hk.2.2 n n' hl) (key n us (by rw [hq]; rfl))

/-! ### Walks that are the identity -/

/-- The walk is the identity at an `fvar` (its type annotation is NOT
visited). -/
theorem restoreWalk_fvar {R : RestoreTbl} {d i : Nat} {ty : Expr} :
    restoreWalk R d (.fvar i ty) = .ok (.fvar i ty) := by
  rcases Bool.eq_false_or_eq_true (R.auxNames.any fun n => (Expr.fvar i ty).mentionsConst n)
    with hp | hp
  · simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false, restoreNode_fvar]
  · simp only [restoreWalk, hp, Bool.not_false, if_pos]

/-- The walk is the identity at a `bvar`. -/
theorem restoreWalk_bvar {R : RestoreTbl} {d i : Nat} :
    restoreWalk R d (.bvar i) = .ok (.bvar i) :=
  restoreWalk_of_no_aux _ _ (fun _ _ => rfl)

/-- The walk is the identity at a sort. -/
theorem restoreWalk_sort {R : RestoreTbl} {d : Nat} {u : Level} :
    restoreWalk R d (.sort u) = .ok (.sort u) :=
  restoreWalk_of_no_aux _ _ (fun _ _ => rfl)

/-- The walk is the identity at a literal. -/
theorem restoreWalk_lit {R : RestoreTbl} {d : Nat} {l : Literal} :
    restoreWalk R d (.lit l) = .ok (.lit l) :=
  restoreWalk_of_no_aux _ _ (fun _ _ => rfl)

/-- **An auxiliary-free term opens to its own restoration**: the prune
may well fail on `e.instantiate1 (.fvar k ty) j` (`mentionsConst`
descends into an `fvar`'s type annotation), but every node step still
declines, so the walk rebuilds the term unchanged. -/
theorem restoreWalk_inst_id {R : RestoreTbl} (hk : R.KeysInAux) {k : Nat} {tyv : Expr} :
    ∀ (e : Expr) (j d : Nat), (∀ n ∈ R.auxNames, e.mentionsConst n = false) →
      restoreWalk R d (e.instantiate1 (.fvar k tyv) j)
        = .ok (e.instantiate1 (.fvar k tyv) j) := by
  intro e
  induction e with
  | bvar i =>
    intro j d _
    simp only [Expr.instantiate1]
    split
    · exact restoreWalk_fvar
    · split <;> exact restoreWalk_bvar
  | fvar i ty => intro j d _; exact restoreWalk_fvar
  | sort u => intro j d _; exact restoreWalk_sort
  | lit l => intro j d _; exact restoreWalk_lit
  | const n us =>
    intro j d hfree
    have hnode : restoreNode R d ((Expr.const n us).instantiate1 (.fvar k tyv) j) = .ok none :=
      restoreNode_none_of_aux_free hk hfree
        (fun n us hq => Expr.getAppFn_const_of_instantiate1 hq)
    rcases Bool.eq_false_or_eq_true
        (R.auxNames.any fun m => ((Expr.const n us).instantiate1 (.fvar k tyv) j).mentionsConst m)
      with hp | hp
    · simp only [Expr.instantiate1] at hnode hp ⊢
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false, hnode]
    · exact restoreWalk_of_no_aux _ _ (auxNames_mention_false hp)
  | app f a ihf iha =>
    intro j d hfree
    have hf : ∀ n ∈ R.auxNames, f.mentionsConst n = false := fun n hn => by
      have h1 := hfree n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h1
      exact h1.1
    have ha : ∀ n ∈ R.auxNames, a.mentionsConst n = false := fun n hn => by
      have h1 := hfree n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h1
      exact h1.2
    have hnode : restoreNode R d ((Expr.app f a).instantiate1 (.fvar k tyv) j) = .ok none :=
      restoreNode_none_of_aux_free hk hfree
        (fun n us hq => Expr.getAppFn_const_of_instantiate1 hq)
    rcases Bool.eq_false_or_eq_true
        (R.auxNames.any fun m => ((Expr.app f a).instantiate1 (.fvar k tyv) j).mentionsConst m)
      with hp | hp
    · simp only [Expr.instantiate1] at hnode hp ⊢
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false, hnode,
        ihf j d hf, iha j d ha]
    · exact restoreWalk_of_no_aux _ _ (auxNames_mention_false hp)
  | lam ty b bm ihty ihb =>
    intro j d hfree
    have hty : ∀ n ∈ R.auxNames, ty.mentionsConst n = false := fun n hn => by
      have h1 := hfree n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h1
      exact h1.1
    have hb : ∀ n ∈ R.auxNames, b.mentionsConst n = false := fun n hn => by
      have h1 := hfree n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h1
      exact h1.2
    have hnode : restoreNode R d ((Expr.lam ty b bm).instantiate1 (.fvar k tyv) j) = .ok none :=
      restoreNode_none_of_aux_free hk hfree
        (fun n us hq => Expr.getAppFn_const_of_instantiate1 hq)
    rcases Bool.eq_false_or_eq_true
        (R.auxNames.any fun m => ((Expr.lam ty b bm).instantiate1 (.fvar k tyv) j).mentionsConst m)
      with hp | hp
    · simp only [Expr.instantiate1] at hnode hp ⊢
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false, hnode,
        ihty j d hty, ihb (j + 1) (d + 1) hb]
    · exact restoreWalk_of_no_aux _ _ (auxNames_mention_false hp)
  | forallE ty b bm ihty ihb =>
    intro j d hfree
    have hty : ∀ n ∈ R.auxNames, ty.mentionsConst n = false := fun n hn => by
      have h1 := hfree n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h1
      exact h1.1
    have hb : ∀ n ∈ R.auxNames, b.mentionsConst n = false := fun n hn => by
      have h1 := hfree n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h1
      exact h1.2
    have hnode : restoreNode R d ((Expr.forallE ty b bm).instantiate1 (.fvar k tyv) j)
        = .ok none :=
      restoreNode_none_of_aux_free hk hfree
        (fun n us hq => Expr.getAppFn_const_of_instantiate1 hq)
    rcases Bool.eq_false_or_eq_true
        (R.auxNames.any fun m =>
          ((Expr.forallE ty b bm).instantiate1 (.fvar k tyv) j).mentionsConst m)
      with hp | hp
    · simp only [Expr.instantiate1] at hnode hp ⊢
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false, hnode,
        ihty j d hty, ihb (j + 1) (d + 1) hb]
    · exact restoreWalk_of_no_aux _ _ (auxNames_mention_false hp)
  | letE ty vl b ihty ihv ihb =>
    intro j d hfree
    have hty : ∀ n ∈ R.auxNames, ty.mentionsConst n = false := fun n hn => by
      have h1 := hfree n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h1
      exact h1.1.1
    have hv : ∀ n ∈ R.auxNames, vl.mentionsConst n = false := fun n hn => by
      have h1 := hfree n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h1
      exact h1.1.2
    have hb : ∀ n ∈ R.auxNames, b.mentionsConst n = false := fun n hn => by
      have h1 := hfree n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h1
      exact h1.2
    have hnode : restoreNode R d ((Expr.letE ty vl b).instantiate1 (.fvar k tyv) j) = .ok none :=
      restoreNode_none_of_aux_free hk hfree
        (fun n us hq => Expr.getAppFn_const_of_instantiate1 hq)
    rcases Bool.eq_false_or_eq_true
        (R.auxNames.any fun m => ((Expr.letE ty vl b).instantiate1 (.fvar k tyv) j).mentionsConst m)
      with hp | hp
    · simp only [Expr.instantiate1] at hnode hp ⊢
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false, hnode,
        ihty j d hty, ihv j d hv, ihb (j + 1) (d + 1) hb]
    · exact restoreWalk_of_no_aux _ _ (auxNames_mention_false hp)
  | proj sn i pe ih =>
    intro j d hfree
    have hpe : ∀ n ∈ R.auxNames, pe.mentionsConst n = false := fun n hn => by
      have h1 := hfree n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h1
      exact h1.2
    have hnode : restoreNode R d ((Expr.proj sn i pe).instantiate1 (.fvar k tyv) j) = .ok none :=
      restoreNode_none_of_aux_free hk hfree
        (fun n us hq => Expr.getAppFn_const_of_instantiate1 hq)
    rcases Bool.eq_false_or_eq_true
        (R.auxNames.any fun m => ((Expr.proj sn i pe).instantiate1 (.fvar k tyv) j).mentionsConst m)
      with hp | hp
    · simp only [Expr.instantiate1] at hnode hp ⊢
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false, hnode, ih j d hpe]
    · exact restoreWalk_of_no_aux _ _ (auxNames_mention_false hp)


/-- Opening a binder does not silence the prune. -/
theorem auxNames_any_instantiate1 {R : RestoreTbl} {e v : Expr} {j : Nat}
    (hp : (R.auxNames.any fun n => e.mentionsConst n) = true) :
    (R.auxNames.any fun n => (e.instantiate1 v j).mentionsConst n) = true := by
  simp only [List.any_eq_true] at hp ⊢
  obtain ⟨n, hn, hm⟩ := hp
  exact ⟨n, hn, Expr.mentionsConst_instantiate1 hm⟩

/-- **The commutation with opening a binder, at cursor `j`**: the walk's
depth and the substitution's cursor move together, which is what lets a
fired pin's lift lose exactly one level. -/
theorem restoreWalk_instantiate1_fvar_at {R : RestoreTbl} (hk : R.KeysInAux) {k : Nat}
    {tyv : Expr} (d : Nat) : ∀ (b : Expr) (j : Nat) (b' : Expr),
      restoreWalk R (d + 1 + j) b = .ok b' →
      restoreWalk R (d + j) (b.instantiate1 (.fvar k tyv) j)
        = .ok (b'.instantiate1 (.fvar k tyv) j) := by
  intro b
  induction b with
  | bvar i =>
    intro j b' h
    have hfree : ∀ n ∈ R.auxNames, (Expr.bvar i).mentionsConst n = false := fun _ _ => rfl
    rw [restoreWalk_of_no_aux _ _ hfree] at h
    obtain rfl := Except.ok.inj h
    exact restoreWalk_inst_id hk _ j (d + j) hfree
  | sort u =>
    intro j b' h
    have hfree : ∀ n ∈ R.auxNames, (Expr.sort u).mentionsConst n = false := fun _ _ => rfl
    rw [restoreWalk_of_no_aux _ _ hfree] at h
    obtain rfl := Except.ok.inj h
    exact restoreWalk_inst_id hk _ j (d + j) hfree
  | lit l =>
    intro j b' h
    have hfree : ∀ n ∈ R.auxNames, (Expr.lit l).mentionsConst n = false := fun _ _ => rfl
    rw [restoreWalk_of_no_aux _ _ hfree] at h
    obtain rfl := Except.ok.inj h
    exact restoreWalk_inst_id hk _ j (d + j) hfree
  | fvar i ty =>
    intro j b' h
    rw [restoreWalk_fvar] at h
    obtain rfl := Except.ok.inj h
    exact restoreWalk_fvar
  | const n us =>
    intro j b' h
    rcases Bool.eq_false_or_eq_true (R.auxNames.any fun m => (Expr.const n us).mentionsConst m)
      with hp | hp
    · have hp' := auxNames_any_instantiate1 (v := .fvar k tyv) (j := j) hp
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hn : restoreNode R (d + 1 + j) (Expr.const n us) with
      | error err => rw [hn] at h; simp at h
      | ok o =>
        have hn' := restoreNode_inst (k := k) (tyv := tyv) hn
        rw [hn] at h
        cases o with
        | some x =>
          simp only at h
          obtain rfl := Except.ok.inj h
          simp only [Expr.instantiate1] at hp' hn' ⊢
          simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
            Option.map_some]
        | none =>
          simp only at h
          obtain rfl := Except.ok.inj h
          simp only [Expr.instantiate1] at hp' hn' ⊢
          simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
            Option.map_none]
    · have hfree := auxNames_mention_false hp
      rw [restoreWalk_of_no_aux _ _ hfree] at h
      obtain rfl := Except.ok.inj h
      exact restoreWalk_inst_id hk _ j (d + j) hfree
  | app f a ihf iha =>
    intro j b' h
    rcases Bool.eq_false_or_eq_true (R.auxNames.any fun m => (Expr.app f a).mentionsConst m)
      with hp | hp
    · have hp' := auxNames_any_instantiate1 (v := .fvar k tyv) (j := j) hp
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hn : restoreNode R (d + 1 + j) (Expr.app f a) with
      | error err => rw [hn] at h; simp at h
      | ok o =>
        have hn' := restoreNode_inst (k := k) (tyv := tyv) hn
        rw [hn] at h
        cases o with
        | some x =>
          simp only at h
          obtain rfl := Except.ok.inj h
          simp only [Expr.instantiate1] at hp' hn' ⊢
          simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
            Option.map_some]
        | none =>
          simp only at h
          cases hf : restoreWalk R (d + 1 + j) f with
          | error err => rw [hf] at h; simp at h
          | ok f' =>
            rw [hf] at h
            cases ha : restoreWalk R (d + 1 + j) a with
            | error err => rw [ha] at h; simp at h
            | ok a' =>
              rw [ha] at h
              obtain rfl := Except.ok.inj h
              simp only [Expr.instantiate1] at hp' hn' ⊢
              simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
                ihf j f' hf, iha j a' ha, Option.map_none]
    · have hfree := auxNames_mention_false hp
      rw [restoreWalk_of_no_aux _ _ hfree] at h
      obtain rfl := Except.ok.inj h
      exact restoreWalk_inst_id hk _ j (d + j) hfree
  | lam ty b bm ihty ihb =>
    intro j b' h
    rcases Bool.eq_false_or_eq_true (R.auxNames.any fun m => (Expr.lam ty b bm).mentionsConst m)
      with hp | hp
    · have hp' := auxNames_any_instantiate1 (v := .fvar k tyv) (j := j) hp
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hn : restoreNode R (d + 1 + j) (Expr.lam ty b bm) with
      | error err => rw [hn] at h; simp at h
      | ok o =>
        have hn' := restoreNode_inst (k := k) (tyv := tyv) hn
        rw [hn] at h
        cases o with
        | some x =>
          simp only at h
          obtain rfl := Except.ok.inj h
          simp only [Expr.instantiate1] at hp' hn' ⊢
          simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
            Option.map_some]
        | none =>
          simp only at h
          cases hty : restoreWalk R (d + 1 + j) ty with
          | error err => rw [hty] at h; simp at h
          | ok ty' =>
            rw [hty] at h
            cases hb : restoreWalk R (d + 1 + j + 1) b with
            | error err => rw [hb] at h; simp at h
            | ok b₁ =>
              rw [hb] at h
              obtain rfl := Except.ok.inj h
              have hbb : restoreWalk R (d + j + 1) (b.instantiate1 (.fvar k tyv) (j + 1))
                  = .ok (b₁.instantiate1 (.fvar k tyv) (j + 1)) := ihb (j + 1) b₁ hb
              simp only [Expr.instantiate1] at hp' hn' ⊢
              simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
                ihty j ty' hty, hbb, Option.map_none]
    · have hfree := auxNames_mention_false hp
      rw [restoreWalk_of_no_aux _ _ hfree] at h
      obtain rfl := Except.ok.inj h
      exact restoreWalk_inst_id hk _ j (d + j) hfree
  | forallE ty b bm ihty ihb =>
    intro j b' h
    rcases Bool.eq_false_or_eq_true
        (R.auxNames.any fun m => (Expr.forallE ty b bm).mentionsConst m) with hp | hp
    · have hp' := auxNames_any_instantiate1 (v := .fvar k tyv) (j := j) hp
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hn : restoreNode R (d + 1 + j) (Expr.forallE ty b bm) with
      | error err => rw [hn] at h; simp at h
      | ok o =>
        have hn' := restoreNode_inst (k := k) (tyv := tyv) hn
        rw [hn] at h
        cases o with
        | some x =>
          simp only at h
          obtain rfl := Except.ok.inj h
          simp only [Expr.instantiate1] at hp' hn' ⊢
          simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
            Option.map_some]
        | none =>
          simp only at h
          cases hty : restoreWalk R (d + 1 + j) ty with
          | error err => rw [hty] at h; simp at h
          | ok ty' =>
            rw [hty] at h
            cases hb : restoreWalk R (d + 1 + j + 1) b with
            | error err => rw [hb] at h; simp at h
            | ok b₁ =>
              rw [hb] at h
              obtain rfl := Except.ok.inj h
              have hbb : restoreWalk R (d + j + 1) (b.instantiate1 (.fvar k tyv) (j + 1))
                  = .ok (b₁.instantiate1 (.fvar k tyv) (j + 1)) := ihb (j + 1) b₁ hb
              simp only [Expr.instantiate1] at hp' hn' ⊢
              simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
                ihty j ty' hty, hbb, Option.map_none]
    · have hfree := auxNames_mention_false hp
      rw [restoreWalk_of_no_aux _ _ hfree] at h
      obtain rfl := Except.ok.inj h
      exact restoreWalk_inst_id hk _ j (d + j) hfree
  | letE ty vl b ihty ihv ihb =>
    intro j b' h
    rcases Bool.eq_false_or_eq_true (R.auxNames.any fun m => (Expr.letE ty vl b).mentionsConst m)
      with hp | hp
    · have hp' := auxNames_any_instantiate1 (v := .fvar k tyv) (j := j) hp
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hn : restoreNode R (d + 1 + j) (Expr.letE ty vl b) with
      | error err => rw [hn] at h; simp at h
      | ok o =>
        have hn' := restoreNode_inst (k := k) (tyv := tyv) hn
        rw [hn] at h
        cases o with
        | some x =>
          simp only at h
          obtain rfl := Except.ok.inj h
          simp only [Expr.instantiate1] at hp' hn' ⊢
          simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
            Option.map_some]
        | none =>
          simp only at h
          cases hty : restoreWalk R (d + 1 + j) ty with
          | error err => rw [hty] at h; simp at h
          | ok ty' =>
            rw [hty] at h
            cases hv : restoreWalk R (d + 1 + j) vl with
            | error err => rw [hv] at h; simp at h
            | ok v' =>
              rw [hv] at h
              cases hb : restoreWalk R (d + 1 + j + 1) b with
              | error err => rw [hb] at h; simp at h
              | ok b₁ =>
                rw [hb] at h
                obtain rfl := Except.ok.inj h
                have hbb : restoreWalk R (d + j + 1) (b.instantiate1 (.fvar k tyv) (j + 1))
                    = .ok (b₁.instantiate1 (.fvar k tyv) (j + 1)) := ihb (j + 1) b₁ hb
                simp only [Expr.instantiate1] at hp' hn' ⊢
                simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
                  ihty j ty' hty, ihv j v' hv, hbb, Option.map_none]
    · have hfree := auxNames_mention_false hp
      rw [restoreWalk_of_no_aux _ _ hfree] at h
      obtain rfl := Except.ok.inj h
      exact restoreWalk_inst_id hk _ j (d + j) hfree
  | proj sn i pe ih =>
    intro j b' h
    rcases Bool.eq_false_or_eq_true (R.auxNames.any fun m => (Expr.proj sn i pe).mentionsConst m)
      with hp | hp
    · have hp' := auxNames_any_instantiate1 (v := .fvar k tyv) (j := j) hp
      simp only [restoreWalk, hp, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hn : restoreNode R (d + 1 + j) (Expr.proj sn i pe) with
      | error err => rw [hn] at h; simp at h
      | ok o =>
        have hn' := restoreNode_inst (k := k) (tyv := tyv) hn
        rw [hn] at h
        cases o with
        | some x =>
          simp only at h
          obtain rfl := Except.ok.inj h
          simp only [Expr.instantiate1] at hp' hn' ⊢
          simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
            Option.map_some]
        | none =>
          simp only at h
          cases hpe : restoreWalk R (d + 1 + j) pe with
          | error err => rw [hpe] at h; simp at h
          | ok pe' =>
            rw [hpe] at h
            obtain rfl := Except.ok.inj h
            simp only [Expr.instantiate1] at hp' hn' ⊢
            simp only [restoreWalk, hp', Bool.not_true, Bool.false_eq_true, if_false, hn',
              ih j pe' hpe, Option.map_none]
    · have hfree := auxNames_mention_false hp
      rw [restoreWalk_of_no_aux _ _ hfree] at h
      obtain rfl := Except.ok.inj h
      exact restoreWalk_inst_id hk _ j (d + j) hfree

/-- **The commutation with opening a binder**: walking a body one binder
deep and then opening it is opening it and then walking. -/
theorem restoreWalk_instantiate1_fvar {R : RestoreTbl} (hk : R.KeysInAux) :
    ∀ (d : Nat) (b b' : Expr) (k : Nat) (ty : Expr),
      restoreWalk R (d + 1) b = .ok b' →
      restoreWalk R d (b.instantiate1 (.fvar k ty)) = .ok (b'.instantiate1 (.fvar k ty)) := by
  intro d b b' k ty h
  exact restoreWalk_instantiate1_fvar_at hk d b 0 b' h

/-! ## K.37's edge list, inverted (task #315, lane L-E's DESIGN §U.55 (a))

K.37's clauses are about the EDGE LIST; the model reads its copy-field
targets off the shape.  This is the bridge: a field the auxiliary block
classified `.recursive`/`.reflexive` at a target OUTSIDE the block's own
members IS an edge of `nestedPinEdges`, with the `own` bit the builder
computes — `mentionsMember` of the container's own group names at the
CONTAINER's stored field domain, which is `true` exactly at a field the
container's own elimination pinned and `false` at an `ordF`-right one.
Every hypothesis is one of `nestedPinEdges`' own lookups, so the model
supplies them from the same reads K.32 already makes. -/
theorem nestedPinEdges_mem {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored} {edges : List (Nat × Nat × Bool)}
    {kinds : List (List (List (RecFieldKind × Nat)))}
    (hedges : nestedPinEdges env p b st stored = some edges)
    (hkinds : nestedPinKinds p b stored = some kinds)
    {q : Nat} (hq : q < st.pins.length)
    {qn : NestedPin} (hqn : st.pins[q]? = some qn)
    {ks : List (List (RecFieldKind × Nat))} (hks : kinds[q]? = some ks)
    {a : AuxStored} (ha : stored[p.k + q]? = some a)
    {ci : ContainerInfo} (hci : containerInfo? env qn.container = some ci)
    {J : ContainerMember} (hJ : ci.members[q - qn.grpBase]? = some J)
    {j : Nat} (hj : j < ks.length)
    {kf : List (RecFieldKind × Nat)} (hkf : ks[j]? = some kf)
    {c : ConstantVal × Nat × Nat} (hc : a.ctors[j]? = some c)
    {cJ : ContainerCtor} (hcJ : J.ctors[j]? = some cJ)
    {jbs : List (Expr × BinderMeta)} {res : Expr}
    (hstrip : cJ.type.stripPis (ci.nP + cJ.nFields) = some (jbs, res))
    {l : Nat} (hl : l < kf.length) {r : RecFieldKind} {t : Nat}
    (hkfl : kf[l]? = some (r, t))
    (hrec : (r == RecFieldKind.recursive || r == RecFieldKind.reflexive) = true)
    (hge : p.k ≤ t)
    {domJ : Expr × BinderMeta} (hdom : jbs[ci.nP + l]? = some domJ) :
    (q, t - p.k, mentionsMember (ci.members.map (·.name)) domJ.1) ∈ edges := by
  have hrange : ∀ {n i : Nat}, i < n → (List.range n)[i]? = some i := by
    intro n i h; simp [h]
  rw [nestedPinEdges, nestedPinEdgesAt] at hedges
  simp only [hkinds, bind, Option.bind] at hedges
  split at hedges
  case h_1 => exact absurd hedges (by simp)
  rename_i rows hrows
  simp only [pure, Option.some.injEq] at hedges
  subst hedges
  -- the row of pin `q`
  obtain ⟨rowq, hrowq, hFq⟩ := mapM_option_inv hrows q q (hrange hq)
  refine List.mem_flatten.mpr ⟨rowq, List.mem_of_getElem? hrowq, ?_⟩
  simp only [hqn, hks, ha, hci, hJ] at hFq
  split at hFq
  case h_1 => exact absurd hFq (by simp)
  rename_i perCtor hperCtor
  simp only [pure, Option.some.injEq] at hFq
  subst hFq
  -- the row of constructor `j`
  obtain ⟨rowj, hrowj, hGj⟩ := mapM_option_inv hperCtor j j (hrange hj)
  refine List.mem_flatten.mpr ⟨rowj, List.mem_of_getElem? hrowj, ?_⟩
  simp only [hkf, hc, hcJ, hstrip] at hGj
  split at hGj
  case h_1 => exact absurd hGj (by simp)
  rename_i perField hperField
  simp only [pure, Option.some.injEq] at hGj
  subst hGj
  -- the row of field `l`
  obtain ⟨rowl, hrowl, hHl⟩ := mapM_option_inv hperField l l (hrange hl)
  refine List.mem_flatten.mpr ⟨rowl, List.mem_of_getElem? hrowl, ?_⟩
  simp only [hkfl, hrec, hge, hdom, decide_true, Bool.and_self, if_true,
    pure, Option.some.injEq] at hHl
  subst hHl
  simp

/-! ## K.41's PIN PAIRING, INVERTED (task #315, lane L-E's DESIGN §U.64 (d) 2)

K.41's Bool is stated over `List.range st.pins.length` and reads the
root group off `nestedPinRootGroup`; the model consumes it at ONE pin of
ONE container instance.  These two theorems are that shape.

The first says the root group is a function of the INSTANCE, so that
"the instance rooted at `r`" and "the root group of `q`" are one
quantifier — `nestedPinRootGroup` reads nothing of a pin but its
instance label.  The second is the pairing: at a pin of the instance,
either the pin is one of the root GROUP's own members, or its pin TERM
is one the root container's own elimination minted, at the root pin's
own level arguments and components — all four of `ClassPin`'s data
(`name` the head, `psi` the levels, `frame` the components, `idx` a
function of the three) in that ONE membership.  Every datum is one of
`nestedPinRootPairOk`'s own lookups, so this costs no new check. -/

theorem getD_map_range_lt {α : Type _} {n i : Nat} (f : Nat → α) (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem nestedPinRootGroupAt_congr {p : NestedParts} {st : ElimState} {inst : List Nat}
    {q r : Nat} (hq : q < st.pins.length) (hr : r < st.pins.length)
    (h : inst.getD q 0 = inst.getD r 0) :
    (nestedPinRootGroupAt p st inst).getD q none
      = (nestedPinRootGroupAt p st inst).getD r none := by
  rw [nestedPinRootGroupAt]
  simp only [getD_map_range_lt _ _ hq, getD_map_range_lt _ _ hr, h]

theorem nestedPinRootGroup_congr {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored} {q r : Nat}
    (hq : q < st.pins.length) (hr : r < st.pins.length)
    (h : (nestedPinInstOf env p b st stored).getD q 0
        = (nestedPinInstOf env p b st stored).getD r 0) :
    (nestedPinRootGroup env p b st stored).getD q none
      = (nestedPinRootGroup env p b st stored).getD r none :=
  nestedPinRootGroupAt_congr hq hr h

theorem nestedPinRootPairAt_inv {env : Env} {st : ElimState} {roots : List (Option Nat)}
    (h : nestedPinRootPairAt env st roots = true) {q : Nat} (hq : q < st.pins.length) :
    ∃ g : Nat, roots.getD q none = some g ∧
      ((st.pins.getD q default).grpBase = g ∨
        ∃ (i : Nat) (lvls : List Level) (Ds own : List Expr),
          i < st.pins.length ∧
          (st.pins.getD i default).grpBase = g ∧
          nestedPinLvlsDs env (st.pins.getD i default) = some (lvls, Ds) ∧
          containerOwnPinsAt env (st.pins.getD i default).container lvls Ds = some own ∧
          (st.pins.getD q default).pin ∈ own) := by
  rw [nestedPinRootPairAt] at h
  simp only [List.all_eq_true] at h
  have hb := h q (List.mem_range.mpr hq)
  split at hb
  · simp at hb
  · rename_i g hg
    refine ⟨g, hg, ?_⟩
    by_cases hgb : ((st.pins.getD q default).grpBase == g) = true
    · exact Or.inl (by simpa using hgb)
    · rw [if_neg hgb] at hb
      obtain ⟨pool, hpool, hin⟩ := List.mem_flatten.mp (List.contains_iff_mem.mp hb)
      obtain ⟨i, hi, hfi⟩ := List.mem_filterMap.mp hpool
      split at hfi
      · rename_i hig
        cases hld : nestedPinLvlsDs env (st.pins.getD i default) with
        | none => rw [hld] at hfi; simp at hfi
        | some ld =>
          rw [hld] at hfi
          simp only [Option.bind_some] at hfi
          exact Or.inr ⟨i, ld.1, ld.2, pool, List.mem_range.mp hi, by simpa using hig,
            hld, hfi, hin⟩
      · simp at hfi

theorem nestedPinRootPairOk_inv {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedPinRootPairOk env p b st stored = true) {q : Nat} (hq : q < st.pins.length) :
    ∃ g : Nat, (nestedPinRootGroup env p b st stored).getD q none = some g ∧
      ((st.pins.getD q default).grpBase = g ∨
        ∃ (i : Nat) (lvls : List Level) (Ds own : List Expr),
          i < st.pins.length ∧
          (st.pins.getD i default).grpBase = g ∧
          nestedPinLvlsDs env (st.pins.getD i default) = some (lvls, Ds) ∧
          containerOwnPinsAt env (st.pins.getD i default).container lvls Ds = some own ∧
          (st.pins.getD q default).pin ∈ own) :=
  nestedPinRootPairAt_inv h hq

/-! ## K.37's rank clauses, inverted (task #315, lane L-E's request)

`nestedPinRankOk` (`Kernel/Inductives/NestedInstall.lean`) had ONE use —
`nestedPinChecks_inv`, which stops at the Bool being `true`.  This is the
way in: the edge list EXISTS (the Bool is `false` at `none`, so the
existence is part of the statement, not a side condition), and the four
clauses hold at `nestedPinInstOf`/`nestedPinRankOf`, the two lists the
model reads.

**Clauses (1) and (2) are folded into ONE disjunction on purpose**: the
model never reads an edge's OWNERSHIP bit.  An own edge gives the
instance equality, a not-own edge gives the disjunction, and the
consumer's conclusion is the disjunction either way — so the edge
relation may be `∃ own, (q, q', own) ∈ edges` and `mentionsMember` is
never computed on the model side.  That is what keeps this a boolean
inversion with no term traversal, in `nestedPinRootPairAt_inv`'s idiom. -/

theorem nestedPinRankAt_inv {st : ElimState} {edges? : Option (List (Nat × Nat × Bool))}
    (h : nestedPinRankAt st edges? = true) :
    ∃ edges, edges? = some edges ∧
      -- (1)+(2) an edge stays in the instance or DROPS the rank
      (∀ e ∈ edges,
        (nestedPinInstAt st edges?).getD e.1 0 = (nestedPinInstAt st edges?).getD e.2.1 0 ∨
          (nestedPinRankListAt st edges?).getD e.2.1 0
            < (nestedPinRankListAt st edges?).getD e.1 0) ∧
      -- (3) the rank is a function of the instance
      (∀ q t, q < st.pins.length → t < st.pins.length →
        (nestedPinInstAt st edges?).getD q 0 = (nestedPinInstAt st edges?).getD t 0 →
        (nestedPinRankListAt st edges?).getD q 0 = (nestedPinRankListAt st edges?).getD t 0) ∧
      -- (4) a mint group is one instance
      (∀ q, q < st.pins.length →
        (nestedPinInstAt st edges?).getD q 0
          = (nestedPinInstAt st edges?).getD (st.pins.getD q default).grpBase 0) := by
  cases hed : edges? with
  | none => rw [hed] at h; simp [nestedPinRankAt] at h
  | some edges =>
  rw [hed] at h
  simp only [nestedPinRankAt, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨-, h3⟩, h4⟩, h12⟩ := h
  refine ⟨edges, rfl, ?_, ?_, ?_⟩
  · intro e he
    have hb := h12 e he
    simp only [nestedPinInstAt, nestedPinRankListAt]
    split at hb
    · exact Or.inl (by simpa using hb)
    · rcases Bool.or_eq_true _ _ |>.mp hb with hb' | hb'
      · exact Or.inl (by simpa using hb')
      · exact Or.inr (by simpa using hb')
  · intro q t hq ht hqt
    simp only [nestedPinInstAt, nestedPinRankListAt] at hqt ⊢
    have hb := h3 q (List.mem_range.mpr hq) t (List.mem_range.mpr ht)
    rcases Bool.or_eq_true _ _ |>.mp hb with hb' | hb'
    · exact absurd (by simpa using hqt) (by simpa using hb')
    · simpa using hb'
  · intro q hq
    have hb := h4 q (List.mem_range.mpr hq)
    simp only [nestedPinInstAt]
    simpa using hb

/-- K.37's clauses at the lists the model reads. -/
theorem nestedPinRankOk_inv {env : Env} {p : NestedParts} {b : MutualBlock}
    {st : ElimState} {stored : List AuxStored}
    (h : nestedPinRankOk env p b st stored = true) :
    ∃ edges, nestedPinEdges env p b st stored = some edges ∧
      (∀ e ∈ edges,
        (nestedPinInstOf env p b st stored).getD e.1 0
            = (nestedPinInstOf env p b st stored).getD e.2.1 0 ∨
          (nestedPinRankOf env p b st stored).getD e.2.1 0
            < (nestedPinRankOf env p b st stored).getD e.1 0) ∧
      (∀ q t, q < st.pins.length → t < st.pins.length →
        (nestedPinInstOf env p b st stored).getD q 0
          = (nestedPinInstOf env p b st stored).getD t 0 →
        (nestedPinRankOf env p b st stored).getD q 0
          = (nestedPinRankOf env p b st stored).getD t 0) ∧
      (∀ q, q < st.pins.length →
        (nestedPinInstOf env p b st stored).getD q 0
          = (nestedPinInstOf env p b st stored).getD
              (st.pins.getD q default).grpBase 0) :=
  nestedPinRankAt_inv h

/-! ## THE RESTORE KEEPS A SPINE'S HEAD A CONSTANT (task #315)

The crossing's premise at the NESTED route: the stored recursor type is
`restoreNested` of the auxiliary block's GENERATED one, whose major
premise's domain is a constant application (`mutualRecTy_majorDom`), and
`restoreWalk_stripPis_doms` carries the telescope positionally — so the
whole obligation is that a walk of a `const`-headed application is
`const`-headed.  MEASURED first, at 284 restored recursors of which 184
are mimics (DESIGN, "THE RESTORE KEEPS THE HEAD A CONSTANT"). -/

/-- **Every table pin is an application of a constant**, at every binder
depth.  It is a property of `restoreTbl`: its pins are
`Expr.abstractRange q.pin 0 nP 0`, and abstracting free variables cannot
change a `const` head.  Carried as a hypothesis here, in the shape the
`ctorPins` fire already uses (`restoreWalk_ctorPin`'s `hhead`). -/
@[expose] def RestoreTbl.PinsHeaded (R : RestoreTbl) : Prop :=
  ∀ n pin, R.pins.lookup n = some pin →
    ∃ J ilvls, ∀ d, (pin.liftLooseBVars d 0).getAppFn = .const J ilvls

/-- **THE NODE STEP KEEPS THE HEAD A CONSTANT**: whichever of the three
maps answers, the replacement is an application of a constant — the pin's
head at a `pins` key (`PinsHeaded`), `newName` at a `ctorPins` key, the
renamed constant at a `recMap` key. -/
theorem restoreHead_head_const {R : RestoreTbl} (hp : R.PinsHeaded) {d : Nat} {e e' : Expr}
    (h : restoreHead R d e = .ok (some e')) :
    ∃ q ls, e'.getAppFn = .const q ls := by
  unfold restoreHead at h
  split at h
  case h_2 => exact nomatch h
  case h_1 n _ _ =>
  simp only [] at h
  split at h
  case h_1 pin hpin =>
    by_cases hl : e.getAppArgs.length < R.nP
    · rw [if_pos hl] at h; exact nomatch h
    · rw [if_neg hl] at h
      obtain ⟨J, ilvls, hJ⟩ := hp n pin hpin
      obtain rfl : Expr.mkAppN (pin.liftLooseBVars d 0) (e.getAppArgs.drop R.nP) = e' :=
        Option.some.inj (Except.ok.inj h)
      exact ⟨J, ilvls, by rw [Expr.getAppFn_mkAppN, hJ]⟩
  case h_2 =>
    split at h
    case h_2 => exact nomatch h
    case h_1 n₀ pin newName hc =>
      by_cases hl : e.getAppArgs.length < R.nP
      · rw [if_pos hl] at h; exact nomatch h
      · rw [if_neg hl] at h
        split at h
        case h_2 => exact nomatch h
        case h_1 J ilvls hJ =>
          refine ⟨newName, ilvls, ?_⟩
          obtain rfl : Expr.mkAppN (Expr.mkAppN (.const newName ilvls)
              (pin.liftLooseBVars d 0).getAppArgs) (e.getAppArgs.drop R.nP) = e' :=
            Option.some.inj (Except.ok.inj h)
          rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN]
          rfl

/-- **THE WALK KEEPS A SPINE'S HEAD A CONSTANT.**  Five cases, four of
them immediate: the PRUNE returns the term, a `recMap` key renames a
constant, the two pin fires are `restoreHead_head_const`, and a
declining node descends componentwise so the head follows the function
part. -/
theorem restoreWalk_getAppFn_const {R : RestoreTbl} (hp : R.PinsHeaded) :
    ∀ (e : Expr) {d : Nat} {e' : Expr} {n : Name} {us : List Level},
      restoreWalk R d e = .ok e' → e.getAppFn = .const n us →
      ∃ q ls, e'.getAppFn = .const q ls := by
  intro e
  induction e with
  | const m ms =>
    intro d e' n us h _
    rcases Bool.eq_false_or_eq_true
        (R.auxNames.any fun m' => (Expr.const m ms).mentionsConst m') with hq | hq
    · simp only [restoreWalk, hq, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hn : restoreNode R d (Expr.const m ms) with
      | error err => rw [hn] at h; exact nomatch h
      | ok o =>
        rw [hn] at h
        match o, h with
        | some e₀, h =>
          obtain rfl : e₀ = e' := Except.ok.inj h
          rw [restoreNode_const] at hn
          split at hn
          case h_1 m' hm' =>
            exact ⟨m', ms, by rw [← Option.some.inj (Except.ok.inj hn)]; rfl⟩
          case h_2 => exact restoreHead_head_const hp hn
        | none, h => exact ⟨m, ms, by rw [← Except.ok.inj h]; rfl⟩
    · simp only [restoreWalk, hq, Bool.not_false, if_pos] at h
      exact ⟨m, ms, by rw [← Except.ok.inj h]; rfl⟩
  | app f a ihf _ =>
    intro d e' n us h hfn
    rcases Bool.eq_false_or_eq_true
        (R.auxNames.any fun m' => (Expr.app f a).mentionsConst m') with hq | hq
    · simp only [restoreWalk, hq, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hn : restoreNode R d (Expr.app f a) with
      | error err => rw [hn] at h; exact nomatch h
      | ok o =>
        rw [hn] at h
        match o, h with
        | some e₀, h =>
          obtain rfl : e₀ = e' := Except.ok.inj h
          rw [restoreNode_eq_head (by intro n' us' hq'; exact Expr.noConfusion hq')] at hn
          exact restoreHead_head_const hp hn
        | none, h =>
          cases hf : restoreWalk R d f with
          | error err => rw [hf] at h; exact nomatch h
          | ok f' =>
            rw [hf] at h
            cases ha : restoreWalk R d a with
            | error err => rw [ha] at h; exact nomatch h
            | ok a' =>
              rw [ha] at h
              obtain rfl : Expr.app f' a' = e' := Except.ok.inj h
              obtain ⟨q, ls, hq'⟩ := ihf hf hfn
              exact ⟨q, ls, hq'⟩
    · simp only [restoreWalk, hq, Bool.not_false, if_pos] at h
      exact ⟨n, us, by rw [← Except.ok.inj h]; exact hfn⟩
  | bvar _ => intro d e' n us _ hfn; exact absurd hfn (by simp [Expr.getAppFn])
  | fvar _ _ _ => intro d e' n us _ hfn; exact absurd hfn (by simp [Expr.getAppFn])
  | sort _ => intro d e' n us _ hfn; exact absurd hfn (by simp [Expr.getAppFn])
  | lam _ _ _ _ _ => intro d e' n us _ hfn; exact absurd hfn (by simp [Expr.getAppFn])
  | forallE _ _ _ _ _ => intro d e' n us _ hfn; exact absurd hfn (by simp [Expr.getAppFn])
  | letE _ _ _ _ _ _ => intro d e' n us _ hfn; exact absurd hfn (by simp [Expr.getAppFn])
  | lit _ => intro d e' n us _ hfn; exact absurd hfn (by simp [Expr.getAppFn])
  | proj _ _ _ _ => intro d e' n us _ hfn; exact absurd hfn (by simp [Expr.getAppFn])

/-- **THE PINS' COMPONENTS, INVERTED** (task #315, lane L-E's request):
what the recorded Bool stands for — at every pin, at every component of
its argument spine, the elimination's own rewrite RUNS at the final
state, its answer is the recorded one, and the state does not grow. -/
theorem nestedPinCompsOk_inv {env : Env} {p : NestedParts} {st : ElimState}
    (h : nestedPinCompsOk env p st = true) :
    ∃ (params : List Expr) (pbs₀ : List (Expr × BinderMeta)) (comps : List (List Expr)),
      nestedRewriteData p st = some (params, pbs₀) ∧
      nestedPinCompRewrites env p st params pbs₀ = some comps ∧
      ∀ (q : Nat) (qn : NestedPin), st.pins[q]? = some qn →
        ∃ cs, comps[q]? = some cs ∧
          ∀ (i : Nat) (c : Expr), qn.pin.getAppArgs[i]? = some c →
            ∃ (c' : Expr) (st' : ElimState),
              replaceAllNested env (p.lps.map Level.param) params pbs₀ st c = .ok (c', st') ∧
              cs[i]? = some c' ∧
              st'.types.length = st.types.length ∧ st'.pins.length = st.pins.length := by
  unfold nestedPinCompsOk at h
  cases hdata : nestedRewriteData p st with
  | none => simp only [hdata] at h; exact nomatch h
  | some pd =>
    obtain ⟨params, pbs₀⟩ := pd
    simp only [hdata] at h
    cases hcomps : nestedPinCompRewrites env p st params pbs₀ with
    | none => simp only [hcomps] at h; exact nomatch h
    | some comps =>
      refine ⟨params, pbs₀, comps, rfl, hcomps, ?_⟩
      intro q qn hqn
      unfold nestedPinCompRewrites at hcomps
      obtain ⟨cs, hcs, hstep⟩ := mapM_option_inv hcomps q qn hqn
      refine ⟨cs, hcs, ?_⟩
      intro i c hc
      obtain ⟨c', hc', hstep'⟩ := mapM_option_inv hstep i c hc
      refine ⟨c', ?_⟩
      cases hr : replaceAllNested env (p.lps.map Level.param) params pbs₀ st c with
      | error e => simp only [hr] at hstep'; exact nomatch hstep'
      | ok r =>
        obtain ⟨c'', st'⟩ := r
        simp only [hr] at hstep'
        split at hstep'
        · rename_i hlen
          simp only [Option.some.injEq] at hstep'
          subst hstep'
          simp only [Bool.and_eq_true, beq_iff_eq] at hlen
          exact ⟨st', rfl, hc', hlen.1, hlen.2⟩
        · exact nomatch hstep'

/-- **AND WHICH COPY NAME IS WHICH AUXILIARY INDEX**: no check records
it, because `nestedCopyNames` is POSITIONAL in the elimination's type
list by construction — the `j`-th copy is the `k + j`-th type, and its
three name kinds are in the flattened list.  Recording as a Bool what
construction already gives is a cost with no content. -/
theorem nestedCopyNames_at {k j : Nat} {st : ElimState} {t : AuxType}
    (ht : st.types[k + j]? = some t) :
    (st.types.drop k)[j]? = some t ∧
      t.name ∈ nestedCopyNames k st ∧ t.name.str "rec" ∈ nestedCopyNames k st ∧
      ∀ c ∈ t.ctors, c.1 ∈ nestedCopyNames k st := by
  have hdrop : (st.types.drop k)[j]? = some t := by
    rw [List.getElem?_drop]; exact ht
  have hmem : t ∈ st.types.drop k := List.mem_of_getElem? hdrop
  refine ⟨hdrop, ?_, ?_, ?_⟩
  · exact List.mem_flatMap.mpr ⟨t, hmem, by simp⟩
  · exact List.mem_flatMap.mpr ⟨t, hmem, by simp⟩
  · intro c hc
    exact List.mem_flatMap.mpr ⟨t, hmem, by simp [List.mem_map.mpr ⟨c, hc, rfl⟩]⟩

/-- **THE RESTORED RULES' CONSTRUCTORS ARE THE RECORD'S** (task #315
M8): post-check (c) compares the stream's rules with the restored ones
position for position, and the constructor name is one of the fields it
compares — so the skeleton's rule-constructor list is a function of the
RECORD, not of the restore. -/
theorem nestedRulesOk_ctors {nP k n : Nat} {recTy : Expr} {own : List (Nat × Nat)}
    {srules grules : List RecRule} (h : nestedRulesOk nP k n recTy own srules grules = true) :
    grules.map (·.ctor) = srules.map (·.ctor) := by
  unfold nestedRulesOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hlen, hlen'⟩, hall⟩ := h
  refine List.ext_getElem? ?_
  intro j
  rw [List.getElem?_map, List.getElem?_map]
  by_cases hj : j < own.length
  · have hstep := hall j (List.mem_range.mpr hj)
    cases hs : srules[j]? with
    | none =>
      rw [hs] at hstep; simp at hstep
    | some a =>
      cases hgg : grules[j]? with
      | none => rw [hs, hgg] at hstep; simp at hstep
      | some g =>
        cases ho : own[j]? with
        | none => rw [hs, hgg, ho] at hstep; simp at hstep
        | some q =>
          rw [hs, hgg, ho] at hstep
          simp only [Bool.and_eq_true, beq_iff_eq] at hstep
          simp only [Option.map_some]
          exact congrArg some hstep.1.1.1.1.symm
  · have h1 : grules[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    have h2 : srules[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [h1, h2]

end ConLeche
