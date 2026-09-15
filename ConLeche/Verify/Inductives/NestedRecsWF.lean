module

public import ConLeche.Kernel.Inductives.NestedInstall
public import ConLeche.Verify.EnvWF
public import ConLeche.Verify.Inductives.NestedFacts
public import ConLeche.Verify.Inductives.MutualWF
public import ConLeche.Verify.Inductives.StructWF

public section

/-!
# The nested install: the recursors' stage keeps `EnvWF` (task #279)

The twin of `MutualWF.lean`'s `mutual_recs_wf` for the NESTED route
(`ConLeche/Kernel/Inductives/NestedInstall.lean`), the model lane's
M-D′ D4 input.

The stage is the same shape as the mutual route's: the restored
recursors are provisioned rule-less (`provisionNestedRecs`) so that
every restored rule is scoped at an environment holding all of them,
and then stored with their rules (`storeNestedRecs`).  The provision
and the store cons the same names in the same order onto the same
environment — here read off `nested_stores_provs`, which says the
store's `(cv, mI, rP, rules)` quadruples carry exactly the provision's
`(cv, mI, rP)` triples — so `provisionNestedRecs_store_le` carries a
rule's resolution from the provision to the store and the walk over
the final environment is one `envWF_of_le`.

The novelty over the mutual route is the `.nested` sub-clause of
`ConstWF`'s stored-rule clause: a MIMIC recursor's rule fires with the
constructor's level and parameter instantiations, and
`nestedFireShape_some_inv` reads the whole clause off the guards
`nestedFireShape` itself checked.  A MEMBER's rule fires `.plain` or
`.inert`, so its clause is vacuous — `nested_rec_constWF` takes both
at once, by cases on `isMimic`.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- A thrown step never succeeds. -/
private theorem nrThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact nrThrow_ne_ok (by assumption))
        | (exfalso; exact nrThrow_ne_ok h)
        | (simp at h))

/-! ## The mimic rules' certified fire -/

/-- **The `.nested` sub-clause of `ConstWF`, off `nestedFireShape`'s own
guards**. -/
theorem nestedFireShape_some_inv {envSelf : Env} {lps : List Name} {tyA : Expr}
    {mI rP cnP : Nat} {lvls : List Level} {pins : List Expr}
    (h : nestedFireShape envSelf lps tyA mI rP cnP = some (lvls, pins)) :
    rP ≤ mI ∧
    (∀ l ∈ lvls, l.allParamsDefined lps = true) ∧
    (∀ pin ∈ pins, pin.hasFvar = false ∧
      pin.allLevelParamsDefined lps = true ∧
      pin.constsResolve envSelf = true ∧
      pin.looseBVarsBounded rP = true) ∧
    ∃ pre dom body bm D,
      tyA.stripPis mI = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i)) := by
  unfold nestedFireShape at h
  split at h
  · next hle =>
    split at h
    · next pre dom body bm hsp =>
      split at h
      · next D lvls' hfn =>
        simp only [] at h
        split at h
        · next hcond =>
          obtain ⟨-, htake, hdrop, hpins, hlvls⟩ := hcond
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hle, fun l hl => (List.all_eq_true.mp hlvls) l hl, fun pin hp => ?_,
            pre, dom, body, bm, D, hsp, hfn, ?_⟩
          · have := (List.all_eq_true.mp hpins) pin hp
            simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
            exact ⟨this.1.1.1, this.2, this.1.2, this.1.1.2⟩
          · conv => lhs; rw [← List.take_append_drop cnP dom.getAppArgs]
            rw [beq_iff_eq.mp hdrop]
            exact congrArg (· ++ _) (beq_iff_eq.mp htake)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## The restored rules, with every guard kept -/

/-- **The restored RULES, positionally, with every fact the stage's own
guards give** (the twin of `restoreRules_id`, keeping the scope tests,
the projection-table test, the restored constructor name, the computed
parameter count, the firing mode and the two rescue bits). -/
theorem restoreRules_shape {envR : Env} {R : RestoreTbl} {lps : List Name} {recName : Name}
    {isMimic : Bool} {recTy : Expr} {mI rP F : Nat} :
    ∀ {rules out : List RecRule},
      restoreRules (m := CheckM) (fueledOps mode F) envR R lps recName isMimic recTy mI rP
          rules = .ok out →
      out.length = rules.length ∧
      ∀ (i : Nat) (rl o : RecRule), rules[i]? = some rl → out[i]? = some o →
        restoreNested R rl.rhs = .ok o.rhs ∧
        o.rhs.allLevelParamsDefined lps = true ∧
        o.rhs.constsResolve envR = true ∧
        o.rhs.looseBVarsBounded 0 = true ∧
        o.rhs.hasFvar = false ∧
        o.rhs.projTablesOk envR = true ∧
        o.nfields = rl.nfields ∧
        o.paramsBlind = !isMimic ∧
        (isMimic = false → o.ctor = rl.ctor ∧
          o.fire = (if Expr.recRulePlain recTy mI rP o.ctorParams then RecRuleFire.plain
            else RecRuleFire.inert)) ∧
        (isMimic = true →
          (∃ q, R.ctorPins.find? (fun q => q.1 == rl.ctor) = some q ∧ o.ctor = q.2.2) ∧
          o.fire = (match nestedFireShape envR lps recTy mI rP o.ctorParams with
            | some (lvls, pins) => RecRuleFire.nested lvls pins
            | none => RecRuleFire.inert)) ∧
        -- **the constructor is stored** (task #279 K.24: the fallback became
        -- a verdict) — the restored rule's constructor is a stored
        -- `ctorInfo` at `envR`, whose parameter count the rule carries
        (∃ (cv : ConstantVal) (n nF : Nat),
          envR.find? o.ctor = some (.ctorInfo cv n nF) ∧ o.ctorParams = n) ∧
        o.k = recRuleKOf envR.find? o.ctor ∧
        o.eta = recRuleEtaOf envR.find? recName o.ctor := by
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
    -- K.24: the constructor's record is read positively
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
      simp only [recRuleBits_rhs, recRuleBits_nfields, recRuleBits_ctor,
        recRuleBits_ctorParams, recRuleBits_fire, recRuleBits_paramsBlind,
        recRuleBits_k, recRuleBits_eta]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h1
      refine ⟨hrhs', h1.1.1.1, h1.1.1.2, h1.1.2, h1.2, h2, by trivial, by trivial, ?_, ?_,
        ⟨cvj, cnP, cnF, by simpa using hfind, rfl⟩, by trivial, by trivial⟩
      · intro hm
        subst hm
        exact ⟨rfl, rfl⟩
      · intro hm
        subst hm
        refine ⟨?_, rfl⟩
        simp only [Bool.not_true, Bool.false_or] at h3
        have hsome : (R.ctorPins.find? (fun q => q.1 == rl.ctor)).isSome = true :=
          List.find?_isSome.mpr (List.any_eq_true.mp h3)
        obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
        obtain ⟨a, b, c⟩ := q
        exact ⟨(a, b, c), hq, by rw [if_pos rfl, hq]⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hr ho
      exact hall k rl' o hr ho

/-! ## The provision's and the store's lookups -/

/-- The provision does not answer for a name none of its recursors carries. -/
theorem provisionNestedRecs_find?_of_ne :
    ∀ {l : List (ConstantVal × Nat × Nat)} {env : Env} {n : Name},
      (∀ x ∈ l, n ≠ x.1.name) → (provisionNestedRecs l env).find? n = env.find? n
  | [], _, _, _ => rfl
  | (cvRa, mI, rP) :: rest, env, n, hne => by
    simp only [provisionNestedRecs]
    rw [provisionNestedRecs_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx)),
      Env.find?_cons, if_neg]
    exact fun hc => hne (cvRa, mI, rP) List.mem_cons_self hc.symm

/-- The store does not answer for a name none of its recursors carries. -/
theorem storeNestedRecs_find?_of_ne :
    ∀ {rs : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env} {n : Name},
      (∀ x ∈ rs, n ≠ x.1.name) → (storeNestedRecs rs env).find? n = env.find? n
  | [], _, _, _ => rfl
  | (cvRa, mI, rP, rules) :: rest, env, n, hne => by
    simp only [storeNestedRecs]
    rw [storeNestedRecs_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx)),
      Env.find?_cons, if_neg]
    exact fun hc => hne (cvRa, mI, rP, rules) List.mem_cons_self hc.symm

/-- The store's constants: the environment's own, or one of the stored
recursors. -/
theorem storeNestedRecs_mem :
    ∀ {rs : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env} {c : ConstantInfo},
      c ∈ (storeNestedRecs rs env).consts →
      c ∈ env.consts ∨ ∃ r ∈ rs, c = .recInfo r.1 r.2.1 r.2.2.1 r.2.2.2
  | [], _, _, h => Or.inl h
  | (cvRa, mI, rP, rules) :: rest, env, c, h => by
    simp only [storeNestedRecs] at h
    rcases storeNestedRecs_mem h with hm | ⟨r, hmem, rfl⟩
    · rcases List.mem_cons.mp hm with rfl | hm'
      · exact Or.inr ⟨(cvRa, mI, rP, rules), List.mem_cons_self, rfl⟩
      · exact Or.inl hm'
    · exact Or.inr ⟨r, List.mem_cons_of_mem _ hmem, rfl⟩

/-- The store finds everything the environment it is built on finds. -/
theorem storeNestedRecs_le :
    ∀ {rs : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env} (n : Name),
      (env.find? n).isSome = true →
      ((storeNestedRecs rs env).find? n).isSome = true
  | [], _, _, h => h
  | (cvRa, mI, rP, rules) :: rest, env, n, h => by
    simp only [storeNestedRecs]
    exact storeNestedRecs_le n (find?_isSome_cons h)

/-- **The provision and the store cons the same names**: the recursors
are provisioned rule-less and stored with their rules in the same order
onto lookup-comparable environments, so a rule scoped at the provision
resolves at the store. -/
theorem provisionNestedRecs_store_le :
    ∀ {rs : List (ConstantVal × Nat × Nat × List RecRule)}
      {l : List (ConstantVal × Nat × Nat)} {env env' : Env},
      rs.map (fun r => (r.1, r.2.1, r.2.2.1)) = l →
      (∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) →
      ∀ n, ((provisionNestedRecs l env).find? n).isSome = true →
        ((storeNestedRecs rs env').find? n).isSome = true
  | [], l, _, _, hsp, hf, n, h => by
    obtain rfl := hsp.symm
    exact hf n h
  | (cvRa, mI, rP, rules) :: rest, l, env, env', hsp, hf, n, h => by
    obtain rfl := hsp.symm
    simp only [List.map_cons, provisionNestedRecs] at h
    simp only [storeNestedRecs]
    exact provisionNestedRecs_store_le (rs := rest)
      (env := ⟨.recInfo cvRa mI rP [] :: env.consts⟩)
      (env' := ⟨.recInfo cvRa mI rP rules :: env'.consts⟩) rfl
      (find?_isSome_cons_mono rfl hf) n h

/-! ## The stored triples ARE the provisioned ones -/

/-- One half of the recursor store's list, mapped back to the
provision's triples. -/
theorem nested_prov_map :
    ∀ {cvs : List ConstantVal} {as : List AuxStored} {rss : List (List RecRule)},
      cvs.length = as.length → rss.length = cvs.length →
      ((cvs.zip (as.zip rss)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))).map
          (fun r => (r.1, r.2.1, r.2.2.1))
        = cvs.zip (as.map fun (a : AuxStored) => (a.mI, a.rP)) := by
  intro cvs
  induction cvs with
  | nil => intro as rss _ _; simp
  | cons cv cvs ih =>
    intro as rss h1 h2
    cases as with
    | nil => simp at h1
    | cons a as' =>
      cases rss with
      | nil => simp at h2
      | cons rs rss' =>
        simp only [List.zip_cons_cons, List.map_cons]
        rw [ih (by simpa using h1) (by simpa using h2)]

/-- **The store's triples are the provision's**: the recursors stored
with their rules carry, name for name, the provision's `(cv, mI, rP)`
triples. -/
theorem nested_stores_provs {cvRms cvRns : List ConstantVal}
    {members mimics : List AuxStored} {rulesM rulesN : List (List RecRule)}
    (hM : cvRms.length = members.length) (hRM : rulesM.length = cvRms.length)
    (hN : cvRns.length = mimics.length) (hRN : rulesN.length = cvRns.length) :
    ((cvRms.zip (members.zip rulesM)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
      ++ (cvRns.zip (mimics.zip rulesN)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
      : List (ConstantVal × Nat × Nat × List RecRule)).map
        (fun r => (r.1, r.2.1, r.2.2.1))
      = (cvRms.zip (members.map fun (a : AuxStored) => (a.mI, a.rP)))
        ++ (cvRns.zip (mimics.map fun (a : AuxStored) => (a.mI, a.rP))) := by
  rw [List.map_append, nested_prov_map hM hRM, nested_prov_map hN hRN]

/-! ## The restored recursor types' type-slot facts -/

/-- Every restored recursor type is closed, level-defined, resolving and
bounded at the environment it was checked at (the pre-annotated front
door's own guards). -/
theorem restoreRecTys_typeWF {env : Env} {R : RestoreTbl} {lps : List Name} {F : Nat} :
    ∀ {names : List Name} {as : List AuxStored} {out : List ConstantVal},
      restoreRecTys (m := CheckM) (fueledOps mode F) env R lps names as = .ok out →
      ∀ o ∈ out, o.type.hasFvar = false ∧
        o.type.allLevelParamsDefined o.levelParams = true ∧
        o.type.constsResolve env = true ∧
        o.type.looseBVarsBounded 0 = true := by
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
    · exact checkConstantValPre_typeWF hpre
    · exact ih hrest o ho

/-- A member of a doubly zipped list, positionally. -/
theorem mem_zip_zip_index {α β γ : Type} {as : List α} {bs : List β} {cs : List γ}
    {x : α × β × γ} (h : x ∈ as.zip (bs.zip cs)) :
    ∃ i : Nat, as[i]? = some x.1 ∧ bs[i]? = some x.2.1 ∧ cs[i]? = some x.2.2 := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem h
  obtain ⟨h1, h2⟩ := List.getElem?_zip_eq_some.mp hi
  obtain ⟨h3, h4⟩ := List.getElem?_zip_eq_some.mp h2
  exact ⟨i, h1, h3, h4⟩

/-! ## One stored recursor -/

/-- **One restored recursor is well-formed at the store**: its type
slot is the restore's own (lifted from the pre-block environment), its
rules are `restoreRules`' (lifted from the provision), and the
`.nested` sub-clause is `nestedFireShape`'s certificate — vacuous at a
member's rule, whose fire is `.plain`/`.inert`. -/
theorem nested_rec_constWF {envStore envProv env₂ : Env} {R : RestoreTbl}
    {cv : ConstantVal} {a : AuxStored} {rs : List RecRule} {isMimic : Bool} {F : Nat}
    (hle₂ : ∀ n, (env₂.find? n).isSome = true → (envStore.find? n).isSome = true)
    (hleP : ∀ n, (envProv.find? n).isSome = true → (envStore.find? n).isSome = true)
    (htype : cv.type.hasFvar = false ∧
      cv.type.allLevelParamsDefined cv.levelParams = true ∧
      cv.type.constsResolve env₂ = true ∧ cv.type.looseBVarsBounded 0 = true)
    (hrun : restoreRules (m := CheckM) (fueledOps mode F) envProv R cv.levelParams cv.name
      isMimic cv.type a.mI a.rP a.rules = .ok rs) :
    ConstWF envStore (.recInfo cv a.mI a.rP rs) := by
  obtain ⟨hfv, hlp, hres, hbv⟩ := htype
  obtain ⟨hlen, hall⟩ := restoreRules_shape hrun
  refine structConstWF hfv hlp (Expr.constsResolve_le hle₂ hres) hbv
    (fun _ _ _ heq => nomatch heq) ?_
  intro cv' mI' rP' rules' heq r hr
  injection heq with e1 e2 e3 e4
  subst e1
  subst e2
  subst e3
  subst e4
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hr
  have hjlt : j < a.rules.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  obtain ⟨-, hlpR, hresR, hbvR, hfvR, -, -, -, hno, hyes, -, -, -⟩ :=
    hall j a.rules[j] r (List.getElem?_eq_getElem hjlt) hj
  refine ⟨hfvR, hlpR, Expr.constsResolve_le hleP hresR, hbvR, ?_⟩
  intro lvls pins hfire
  cases isMimic with
  | false =>
    obtain ⟨-, hf⟩ := hno rfl
    rw [hfire] at hf
    split at hf <;> simp at hf
  | true =>
    obtain ⟨-, hf⟩ := hyes rfl
    rw [hfire] at hf
    split at hf
    · next l p hsh =>
      obtain ⟨rfl, rfl⟩ := RecRuleFire.nested.inj hf
      obtain ⟨g1, g2, g3, g4⟩ := nestedFireShape_some_inv hsh
      exact ⟨g1, g2, fun pin hp =>
        let ⟨p1, p2, p3, p4⟩ := g3 pin hp
        ⟨p1, p2, Expr.constsResolve_le hleP p3, p4⟩, g4⟩
    · simp at hf

/-! ## The recursors' stage at the run level -/

/-- **Stage 5/6 at the run level** (the twin of `mutual_recs_wf`): the
restored recursors, stored as a group with their restored rules, keep
the environment well-formed. -/
theorem nested_recs_wf {env₂ : Env} (henv₂ : EnvWF env₂) {R : RestoreTbl} {lps : List Name}
    {namesM namesN : List Name} {members mimics : List AuxStored}
    {cvRms cvRns : List ConstantVal} {rulesM rulesN : List (List RecRule)} {F : Nat}
    (hrm : restoreRecTys (m := CheckM) (fueledOps mode F) env₂ R lps namesM members = .ok cvRms)
    (hrn : restoreRecTys (m := CheckM) (fueledOps mode F) env₂ R lps namesN mimics = .ok cvRns)
    (hrulesM : (cvRms.zip members).mapM (fun (cvRa, a) =>
        restoreRules (m := CheckM) (fueledOps mode F)
          (provisionNestedRecs
            ((cvRms.zip (members.map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip (mimics.map fun (a : AuxStored) => (a.mI, a.rP)))) env₂)
          R cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules) = .ok rulesM)
    (hrulesN : (cvRns.zip mimics).mapM (fun (cvRa, a) =>
        restoreRules (m := CheckM) (fueledOps mode F)
          (provisionNestedRecs
            ((cvRms.zip (members.map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip (mimics.map fun (a : AuxStored) => (a.mI, a.rP)))) env₂)
          R cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules) = .ok rulesN) :
    EnvWF (storeNestedRecs
      ((cvRms.zip (members.zip rulesM)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
        ++ (cvRns.zip (mimics.zip rulesN)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs)))
      env₂) := by
  obtain ⟨hlenM, -⟩ := restoreRecTys_inv hrm
  obtain ⟨hlenN, -⟩ := restoreRecTys_inv hrn
  obtain ⟨hlenRM, hallRM⟩ := mapM_except_inv hrulesM
  obtain ⟨hlenRN, hallRN⟩ := mapM_except_inv hrulesN
  have hzM : (cvRms.zip members).length = cvRms.length := by simp [hlenM]
  have hzN : (cvRns.zip mimics).length = cvRns.length := by simp [hlenN]
  have hRM : rulesM.length = cvRms.length := by rw [hlenRM, hzM]
  have hRN : rulesN.length = cvRns.length := by rw [hlenRN, hzN]
  have hleP := provisionNestedRecs_store_le (env := env₂) (env' := env₂)
    (nested_stores_provs hlenM hRM hlenN hRN) (fun _ h => h)
  refine envWF_of_le henv₂ (fun n => storeNestedRecs_le n) ?_
  intro c hc
  rcases storeNestedRecs_mem hc with hm | ⟨r, hr, rfl⟩
  · exact Or.inl hm
  right
  rcases List.mem_append.mp hr with hr | hr
  · simp only [List.mem_map] at hr
    obtain ⟨⟨cv, a, rs⟩, hx, rfl⟩ := hr
    obtain ⟨i, hi1, hi2, hi3⟩ := mem_zip_zip_index hx
    have hilt : i < (cvRms.zip members).length := by
      rw [hzM]
      have := (List.getElem?_eq_some_iff.mp hi1).1
      omega
    obtain ⟨y, b, hy, hb, hrun⟩ := hallRM i hilt
    obtain rfl : y = (cv, a) :=
      Option.some.inj (hy.symm.trans (List.getElem?_zip_eq_some.mpr ⟨hi1, hi2⟩))
    obtain rfl : b = rs := Option.some.inj (hb.symm.trans hi3)
    exact nested_rec_constWF (fun n => storeNestedRecs_le n) hleP
      (restoreRecTys_typeWF hrm cv (List.mem_of_getElem? hi1)) hrun
  · simp only [List.mem_map] at hr
    obtain ⟨⟨cv, a, rs⟩, hx, rfl⟩ := hr
    obtain ⟨i, hi1, hi2, hi3⟩ := mem_zip_zip_index hx
    have hilt : i < (cvRns.zip mimics).length := by
      rw [hzN]
      have := (List.getElem?_eq_some_iff.mp hi1).1
      omega
    obtain ⟨y, b, hy, hb, hrun⟩ := hallRN i hilt
    obtain rfl : y = (cv, a) :=
      Option.some.inj (hy.symm.trans (List.getElem?_zip_eq_some.mpr ⟨hi1, hi2⟩))
    obtain rfl : b = rs := Option.some.inj (hb.symm.trans hi3)
    exact nested_rec_constWF (fun n => storeNestedRecs_le n) hleP
      (restoreRecTys_typeWF hrn cv (List.mem_of_getElem? hi1)) hrun

end ConLeche
