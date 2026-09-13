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

/-- The pre-annotated front door returns its input: every check of
`checkConstantVal` runs, and the stored type is the input type. -/
theorem checkConstantValPre_ok {env : Env} {cv cvA : ConstantVal} {F : Nat}
    (h : checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvA) :
    cvA = cv := by
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
  try simp only [bind, Except.bind] at h
  obtain ⟨_sty, _hinf, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨_u, _hens, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

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

/-- The formers stage at `auxRoute`, one member, TAIL ONLY: whatever the
front door was, the result is one former per member and the rest of the
list ran. -/
theorem mutualFormerChecks_true_tail {nP F : Nat} {cv : ConstantVal} {nIdx : Nat}
    {rest : List (ConstantVal × Nat)} {env : Env} {fms : List MutualFormerA}
    (h : mutualFormerChecks (fueledOps mode F) env nP true ((cv, nIdx) :: rest) = .ok fms) :
    ∃ (f : MutualFormerA) (fs : List MutualFormerA),
      fms = f :: fs ∧
      mutualFormerChecks (fueledOps mode F) env nP true rest = .ok fs := by
  unfold mutualFormerChecks at h
  simp only [Bool.true_and] at h
  by_cases hp : Name.hasPrefixOf nestedPrefixName cv.name = true
  case pos =>
    rw [if_pos hp] at h
    obtain ⟨_cvTa₀, _hccv, h⟩ := exceptBind_ok h
    obtain ⟨q, _htele, h⟩ := exceptBind_ok h
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
    exact ⟨⟨cvTa, nIdx, s⟩, fs, h.symm, hrec⟩
  case neg =>
    rw [if_neg hp] at h
    obtain ⟨_cvTa₀, _hccv, h⟩ := exceptBind_ok h
    obtain ⟨q, _htele, h⟩ := exceptBind_ok h
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
    exact ⟨⟨cvTa, nIdx, s⟩, fs, h.symm, hrec⟩

/-- The formers stage at `auxRoute`, one `_nested`-named member: the
front door is `checkConstantValPre`, and the stored former is the one
`checkSumTele` returned. -/
theorem mutualFormerChecks_true_head_pre {nP F : Nat} {cv : ConstantVal} {nIdx : Nat}
    {rest : List (ConstantVal × Nat)} {env : Env} {fms : List MutualFormerA}
    (hp : Name.hasPrefixOf nestedPrefixName cv.name = true)
    (h : mutualFormerChecks (fueledOps mode F) env nP true ((cv, nIdx) :: rest) = .ok fms) :
    ∃ (cvTa₀ cvTa : ConstantVal) (s : Level) (fs : List MutualFormerA),
      checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvTa₀ ∧
      checkSumTele (fueledOps mode F) env cv (nP + nIdx) cvTa₀ = .ok (cvTa, s) ∧
      fms = ⟨cvTa, nIdx, s⟩ :: fs := by
  unfold mutualFormerChecks at h
  simp only [Bool.true_and] at h
  rw [if_pos hp] at h
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
  obtain ⟨fs, _hrec, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨cvTa₀, cvTa, s, fs, hccv, htele, h.symm⟩

/-- **THE COPIES' TYPES, READY-MADE** (K.10).  At `auxRoute` a member
whose name carries the reserved `_nested` prefix — i.e. a copy the kernel
minted itself — is STORED WITH THE TYPE IT WAS GIVEN, provided that type
already strips its telescope to a sort, which is exactly what
`auxIdxCount` read off it when `auxBlock` recorded the copy's index
count.  No annotation-stability hypothesis anywhere: the walk does not
run on these members. -/
theorem mutualFormerChecks_true_id {nP F : Nat} {env : Env} :
    ∀ {formers : List (ConstantVal × Nat)} {fms : List MutualFormerA},
      mutualFormerChecks (fueledOps mode F) env nP true formers = .ok fms →
      ∀ (i : Nat) (cv : ConstantVal) (nIdx : Nat),
        formers[i]? = some (cv, nIdx) →
        Name.hasPrefixOf nestedPrefixName cv.name = true →
        (∃ (bs : List (Expr × BinderMeta)) (s : Level),
          cv.type.stripPis (nP + nIdx) = some (bs, Expr.sort s)) →
        ∃ f : MutualFormerA, fms[i]? = some f ∧ f.cvTa.type = cv.type := by
  intro formers
  induction formers with
  | nil =>
    intro fms _h i cv nIdx hi _ _
    exact absurd hi (by simp)
  | cons hd rest ih =>
    intro fms h i cv nIdx hi hp hstrip
    obtain ⟨cv₀, nIdx₀⟩ := hd
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      obtain ⟨cvTa₀, cvTa, s, fs, hfront, htele, rfl⟩ :=
        mutualFormerChecks_true_head_pre hp h
      have e1 := checkConstantValPre_ok hfront
      obtain ⟨bs', s', hs'⟩ := hstrip
      rw [← e1] at hs'
      have e2 := checkSumTele_id hs' htele
      exact ⟨_, rfl, by rw [e2, e1]⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨f₀, fs, rfl, hrec⟩ := mutualFormerChecks_true_tail h
      obtain ⟨f, hf, hft⟩ := ih hrec k cv nIdx hi hp hstrip
      exact ⟨f, by simpa using hf, hft⟩

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

/-- **THE IDENTITY THE MODEL TIER READS OFF THE RUN** (task #279 K.10).

Two of `DeclNestedRun`'s conjuncts — the auxiliary block and its
install in the scratch environment — already say that every COPY (a
member of the re-minted `st.types` whose name carries the reserved
`_nested` prefix) is stored with the type the elimination minted for it,
SYNTACTICALLY.  No annotation-stability premise: the install's formers
stage runs `checkConstantValPre` on such a member (the `auxRoute` grade),
which checks everything `checkConstantVal` checks and returns its input,
and `checkSumTele` returns it unchanged because a copy's type is a
syntactic telescope ending in a sort — which is exactly what
`auxIdxCount` read off it when `auxBlock` recorded the index count.

`env₁ = consMutualFormers fms env` is how the stage stores it, so
`f.cvTa.type = t.type` IS the stored former's type. -/
theorem nestedCopyFormerType_eq {env envAux : Env} {p : NestedParts} {st : ElimState}
    {b : MutualBlock} {F : Nat}
    (hb : auxBlock p st = some b)
    (haux : checkMutualCore (m := CheckM) (fueledOps mode F) env b none true = .ok envAux) :
    ∀ (i : Nat) (t : AuxType), st.types[i]? = some t →
      Name.hasPrefixOf nestedPrefixName t.name = true →
      ∃ (env₁ : Env) (fms : List MutualFormerA) (f : MutualFormerA),
        mutualFormers (fueledOps mode F) b.nP b.formers env true = .ok (env₁, fms) ∧
        env₁ = consMutualFormers fms env ∧
        fms[i]? = some f ∧ f.cvTa.type = t.type := by
  intro i t hi hp
  obtain ⟨hnP, hform⟩ := auxBlock_former hb
  obtain ⟨nIdx, hfi, hcnt⟩ := hform i t hi
  obtain ⟨-, -, -, -, env₁, fms, -, -, -, -, -, -, -, -, -, hformers, -⟩ :=
    checkMutualCore_inv haux
  obtain ⟨hchecks, henv₁⟩ := mutualFormers_inv hformers
  obtain ⟨bs, u, hstrip⟩ := auxIdxCount_stripPis hcnt
  refine ⟨env₁, fms, ?_⟩
  obtain ⟨f, hf, hft⟩ :=
    mutualFormerChecks_true_id hchecks i ⟨t.name, p.lps, t.type⟩ nIdx hfi hp
      ⟨bs, u, by rw [hnP]; exact hstrip⟩
  exact ⟨f, hformers, henv₁, hf, hft⟩

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
      (st₀ : ElimState) (a₀ : AuxStored) (fvsA : List Expr × Expr) (order : List Nat)
      (pinsA : List (NestedPin × Expr)),
      -- the elimination, the re-mint of the copies' types at ANNOTATED
      -- pin components, and the mimic count against the stream's records
      elimNested env p.nP p.lps
        (p.formers.zipIdx.map fun ((cv, _), mIdx) =>
          (⟨cv.name, cv.type,
            (p.ctors.filter (fun c => c.member == mIdx)).map
              fun c => (c.cv.name, c.cv.type, c.nF)⟩ : AuxType)) = .ok st₀ ∧
      nestedRemint (m := CheckM) (fueledOps mode F) env p st₀ = .ok (st, pinsA) ∧
      st.pins.length = p.numNested ∧
      -- every MINTED name is free in the pre-block environment
      copiesFresh env p.k st = true ∧
      -- the copies' REFERENCE RELATION, topologically sorted
      nestedTopoOrder (ElimState.grp st) p.k st = .ok order ∧
      -- the auxiliary mutual block, checked in a SCRATCH environment
      auxBlock p st = some b ∧
      checkMutualCore (m := CheckM) (fueledOps mode F) env b none true = .ok envAux ∧
      auxStoredAll envAux b b.k = some stored ∧
      -- `pinsOkAux`: the pins typed at the SCRATCH environment
      (stored.take p.k).head? = some a₀ ∧
      openPisAtFvars p.nP a₀.cvTa.type 0 = some fvsA ∧
      -- `pinsClosed`: every pin, abstracted over the parameters, is
      -- fvar-free with its loose bvars inside the telescope
      pinsClosed p.nP st.pins = true ∧
      nestedPinsOk (m := CheckM) (fueledOps mode F) envAux p.nP pinsA = .ok () ∧
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
      nestedPinsOk (m := CheckM) (fueledOps mode F) envOut p.nP pinsA = .ok () ∧
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
        = .ok () := by
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
  obtain ⟨st₀, helim, h⟩ := exceptBind_ok h
  have helim' := nestedLift_ok helim
  try simp only at h
  obtain ⟨stp, hrem, h⟩ := exceptBind_ok h
  obtain ⟨st, pinsA⟩ := stp
  try simp only at h
  by_cases hcnt : (st.pins.length == p.numNested) = true
  case neg => rw [if_neg hcnt] at h; close_throw
  rw [if_pos hcnt] at h
  try simp only [bind, Except.bind] at h
  by_cases hfresh : copiesFresh env p.k st = true
  case neg => rw [if_neg hfresh] at h; close_throw
  rw [if_pos hfresh] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨order, hto, h⟩ := exceptBind_ok h
  have hto' := mapError_ok (nestedLift_ok hto)
  try simp only at h
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  have hb' := unwrapOr_ok hb
  try simp only at h
  obtain ⟨envAux, haux, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨stored, hst, h⟩ := exceptBind_ok h
  have hst' := unwrapOr_ok hst
  try simp only at h
  obtain ⟨a₀, ha₀, h⟩ := exceptBind_ok h
  have ha₀' := unwrapOr_ok ha₀
  try simp only at h
  obtain ⟨fvsA, hfv, h⟩ := exceptBind_ok h
  have hfv' := unwrapOr_ok hfv
  try simp only at h
  by_cases hpc : pinsClosed p.nP st.pins = true
  case neg => rw [if_neg hpc] at h; close_throw
  rw [if_pos hpc] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨uA, hpinsAux, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨ctorsR, hctors, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨cvRms, hrm, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨cvRns, hrn, h⟩ := exceptBind_ok h
  try simp only at h
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
  have henv : env₄ = envOut := by
    simpa [pure, Except.pure] using h
  subst henv
  exact ⟨st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, st₀, a₀, fvsA,
    order, pinsA, helim', hrem, beq_iff_eq.mp hcnt, hfresh, hto', hb', haux, hst', ha₀', hfv', hpc,
    (by cases uA; exact hpinsAux), hctors, hrm, hrn, hrlm, hrln, htbl,
    (by cases u₀; exact hpins), hlen, by cases u₁; exact hrecs⟩

end ConLeche
