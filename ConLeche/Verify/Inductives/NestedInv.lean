module

public import ConLeche.Verify.Inductives.MutualInv
public import ConLeche.Kernel.Inductives.NestedInstall

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
      = .ok cvCa ∧ cvC.type.projTablesOk env = true := by
  unfold checkMutualCtor at h
  simp only [if_true] at h
  obtain ⟨cvCa₀, hfront, h⟩ := exceptBind_ok h
  obtain ⟨c, hnorm, h⟩ := exceptBind_ok h
  have hproj := checkConstantValPre_projOk hfront
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
  exact ⟨hnorm, hproj⟩

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
    obtain ⟨hnorm, hproj⟩ := checkMutualCtor_true_norm hrun
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
      -- THE PINS' SCOPE (K.30): the pins' free variables are the first
      -- former's openers, annotation included, and no loose bvar
      certOnly mode (pinsScoped p.nP st) = true ∧
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
      certOnly mode (nestedPinParentOk st) = true ∧
      -- POST-CHECK (a) A THIRD TIME (K.30): the pins typed at the
      -- environment holding the RESTORED formers
      nestedPinsOk (m := CheckM) (fueledOps mode F)
          (consNestedFormers (stored.take p.k) env) p.nP st.pins = .ok () ∧
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
          (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))) = true := by
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
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  have hb' := unwrapOr_ok hb
  try simp only at h
  obtain ⟨envAux, haux, h⟩ := exceptBind_ok h
  try simp only at h
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
  by_cases hsc : certOnly (fueledOps mode F).mode (pinsScoped p.nP st) = true
  case neg => rw [if_neg hsc] at h; close_throw
  rw [if_pos hsc] at h
  try simp only [bind, Except.bind] at h
  by_cases htg : certOnly (fueledOps mode F).mode (nestedCopyTargetsOk env p b st stored) = true
  case neg => rw [if_neg htg] at h; close_throw
  rw [if_pos htg] at h
  try simp only [bind, Except.bind] at h
  by_cases hkd : certOnly (fueledOps mode F).mode (nestedPinKindsOk p b st stored) = true
  case neg => rw [if_neg hkd] at h; close_throw
  rw [if_pos hkd] at h
  try simp only [bind, Except.bind] at h
  by_cases haa : certOnly (fueledOps mode F).mode (nestedAuxAppsOk p st stored) = true
  case neg => rw [if_neg haa] at h; close_throw
  rw [if_pos haa] at h
  try simp only [bind, Except.bind] at h
  by_cases hrk : certOnly (fueledOps mode F).mode (nestedPinRankOk env p b st stored) = true
  case neg => rw [if_neg hrk] at h; close_throw
  rw [if_pos hrk] at h
  try simp only [bind, Except.bind] at h
  by_cases hpa : certOnly (fueledOps mode F).mode (nestedPinParentOk st) = true
  case neg => rw [if_neg hpa] at h; close_throw
  rw [if_pos hpa] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨uP₁, hpins₁, h⟩ := exceptBind_ok h
  try simp only at h
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
  obtain ⟨rulesM, hrlm, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨rulesN, hrln, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨env₄, htbl, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨u₀, hpins, h⟩ := exceptBind_ok h
  try simp only at h
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
  have henv : env₄ = envOut := by
    simpa [pure, Except.pure] using h
  subst henv
  exact ⟨st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, fmsA, ctorsA,
    hfmsA, hctorsA, helim', beq_iff_eq.mp hcnt, hfresh, hcont, hb', haux, hst', hpc,
    (by cases uA; exact hpinsAux), hcaps, hsrc,
    certOnly_and_left hcont, hgrp, hsc, htg, hkd, haa, hrk, hpa,
    (by cases uP₁; exact hpins₁), hctors, hrm, hrn, hnd, hrlm, hrln, htbl,
    (by cases u₀; exact hpins), hlen, (by cases u₁; exact hrecs), hrb⟩

end ConLeche
