module

public import ConLeche.Kernel.Inductives.NestedInstall
public import ConLeche.Verify.Inductives.MutualGrouped
import ConLeche.Verify.Inductives.NestedInv

public section

/-!
# The scratch install's members, read back (task #315 M6 s6)

The nested route installs its auxiliary block with the MUTUAL
installer at the `auxRoute` grade and then reads the stored members
back out of the scratch environment (`auxStored?`,
`ConLeche/Kernel/Inductives/NestedInstall.lean`).  This module proves
that what comes back IS what the formers' stage checked:

* **the prefix run** (`mutualFormerChecksG_take`,
  `mutualFormersG_take`): the formers' checks run every member at the
  SAME pre-block environment, so a prefix of the block checks to the
  prefix of the results — which is what the restore's partial
  environments are compared against;
* **the member records survive the scratch install**
  (`checkMutualCore_find?_indInfo`, `checkMutualCore_member_record`):
  every cons after the formers' is a constructor, a recursor or a
  projection table, so an `indInfo` found at the install's output was
  found at the formers' environment, where the block's `Nodup` names
  it as its own member's;
* **the restored formers' environment**
  (`consNestedFormers_take_eq`): the read-back records cons the very
  environment the formers' stage consed, prefix by prefix;
* **the constructors' records survive it too**
  (`consMutualCtors_find?_self`, `checkMutualCore_ctor_record`): the
  constructors' conses answer at every checked constructor's own name,
  and neither the recursors' group nor the projection tables touches
  that answer — so the read-back at a member's constructors
  (`auxStored?_ctors`) IS the constructors' stage's own run of
  `b.ctors`, positionally (`auxStored_ctor_eq`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## The formers' checks on a prefix -/

/-- The formers' loop at a grade, one member, keeping the DOOR'S RUN
(`mutualFormerChecksG_inv` keeps its facts instead, which does not
rebuild). -/
private theorem formerChecksG_cons_inv {nP F nIdx : Nat} {g : Bool} {cv : ConstantVal}
    {rest : List (ConstantVal × Nat)} {env : Env} {fms : List MutualFormerA}
    (h : mutualFormerChecks (fueledOps mode F) env nP g ((cv, nIdx) :: rest) = .ok fms) :
    ∃ (cvTa₀ cvTa : ConstantVal) (s : Level) (bs : List (Expr × BinderMeta))
      (fs : List MutualFormerA),
      (if g then checkConstantValPre (m := CheckM) (fueledOps mode F) env cv
        else checkConstantVal (fueledOps mode F) env cv) = .ok cvTa₀ ∧
      checkSumTele (fueledOps mode F) env cv (nP + nIdx) cvTa₀ = .ok (cvTa, s) ∧
      cvTa.type.stripPis (nP + nIdx) = some (bs, Expr.sort s) ∧
      mutualFormerChecks (fueledOps mode F) env nP g rest = .ok fs ∧
      fms = ⟨cvTa, nIdx, s⟩ :: fs := by
  unfold mutualFormerChecks at h
  cases g <;> simp only [if_true, Bool.false_eq_true, if_false] at h ⊢
  all_goals
    obtain ⟨cvTa₀, hccv, h⟩ := exceptBind_ok h
    obtain ⟨q, htele, h⟩ := exceptBind_ok h
    obtain ⟨cvTa, s⟩ := q
    try simp only at h
    obtain ⟨q2, hq2, h⟩ := exceptBind_ok h
    obtain ⟨bs, tbody⟩ := q2
    have hq2' := unwrapOr_ok hq2
    try simp only at h
    by_cases hc : (tbody == Expr.sort s) = true
    case neg =>
      exfalso
      rw [if_neg hc] at h
      simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      exact absurd h (by simp)
    rw [if_pos hc] at h
    try simp only [bind, Except.bind] at h
    obtain ⟨fs, hrec, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    exact ⟨cvTa₀, cvTa, s, bs, fs, hccv, htele, by rw [hq2', beq_iff_eq.mp hc], hrec, rfl⟩

/-- The formers' loop at a grade, one member, REBUILT from its steps. -/
private theorem formerChecksG_cons_mk {nP F nIdx : Nat} {g : Bool} {cv cvTa₀ cvTa : ConstantVal}
    {s : Level} {bs : List (Expr × BinderMeta)} {rest : List (ConstantVal × Nat)}
    {env : Env} {fs : List MutualFormerA}
    (hdoor : (if g then checkConstantValPre (m := CheckM) (fueledOps mode F) env cv
        else checkConstantVal (fueledOps mode F) env cv) = .ok cvTa₀)
    (htele : checkSumTele (fueledOps mode F) env cv (nP + nIdx) cvTa₀ = .ok (cvTa, s))
    (hstrip : cvTa.type.stripPis (nP + nIdx) = some (bs, Expr.sort s))
    (hrest : mutualFormerChecks (fueledOps mode F) env nP g rest = .ok fs) :
    mutualFormerChecks (fueledOps mode F) env nP g ((cv, nIdx) :: rest)
      = .ok (⟨cvTa, nIdx, s⟩ :: fs) := by
  unfold mutualFormerChecks
  cases g <;> simp only [if_true, Bool.false_eq_true, if_false] at hdoor ⊢
  all_goals
    rw [hdoor]
    simp only [bind, Except.bind]
    rw [htele]
    simp only [unwrapOr, hstrip, pure, Except.pure, beq_self_eq_true, if_true]
    rw [hrest]

/-- **The formers' checks on a PREFIX**: the loop runs every member at
the same pre-block environment, so a prefix of the block checks to the
prefix of the results. -/
theorem mutualFormerChecksG_take {nP F : Nat} {g : Bool} {env : Env} :
    ∀ {l : List (ConstantVal × Nat)} {fms : List MutualFormerA},
      mutualFormerChecks (fueledOps mode F) env nP g l = .ok fms →
      ∀ k, mutualFormerChecks (fueledOps mode F) env nP g (l.take k) = .ok (fms.take k) := by
  intro l
  induction l with
  | nil =>
    intro fms h k
    obtain rfl := mutualFormerChecksG_nil_inv h
    simp only [List.take_nil]
    exact h
  | cons hd rest ih =>
    intro fms h k
    obtain ⟨cv, nIdx⟩ := hd
    obtain ⟨cvTa₀, cvTa, s, bs, fs, hdoor, htele, hstrip, hrest, rfl⟩ :=
      formerChecksG_cons_inv h
    cases k with
    | zero => simp only [List.take_zero]; rfl
    | succ k =>
      simp only [List.take_succ_cons]
      exact formerChecksG_cons_mk hdoor htele hstrip (ih hrest k)

/-- The formers' stage on a prefix: the prefix of the results, consed. -/
theorem mutualFormersG_take {nP F : Nat} {g : Bool} {env env₁ : Env}
    {formers : List (ConstantVal × Nat)} {fms : List MutualFormerA}
    (h : mutualFormers (fueledOps mode F) nP formers env g = .ok (env₁, fms)) (k : Nat) :
    mutualFormers (fueledOps mode F) nP (formers.take k) env g
      = .ok (consMutualFormers (fms.take k) env, fms.take k) := by
  obtain ⟨hchecks, -⟩ := mutualFormers_inv h
  unfold mutualFormers
  rw [mutualFormerChecksG_take hchecks k]
  rfl

/-- The formers' checks keep the block's length. -/
theorem mutualFormerChecksG_length {nP F : Nat} {g : Bool} {env : Env} :
    ∀ {l : List (ConstantVal × Nat)} {fms : List MutualFormerA},
      mutualFormerChecks (fueledOps mode F) env nP g l = .ok fms → fms.length = l.length := by
  intro l
  induction l with
  | nil => intro fms h; obtain rfl := mutualFormerChecksG_nil_inv h; rfl
  | cons hd rest ih =>
    intro fms h
    obtain ⟨cv, nIdx⟩ := hd
    obtain ⟨cvTa₀, cvTa, s, bs, fs, -, -, -, hrest, rfl⟩ := mutualFormerChecksG_inv h
    simp only [List.length_cons, ih hrest]

/-- **The checked formers, positionally**: the `t`-th checked member is
the `t`-th declared one — its index count and its name the declared
constant's. -/
theorem mutualFormerChecksG_nIdx {nP F : Nat} {g : Bool} {env : Env} :
    ∀ {l : List (ConstantVal × Nat)} {fms : List MutualFormerA},
      mutualFormerChecks (fueledOps mode F) env nP g l = .ok fms →
      ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
        ∃ cv : ConstantVal, l[t]? = some (cv, f.nIdx) ∧ cv.name = f.cvTa.name := by
  intro l
  induction l with
  | nil =>
    intro fms h t f hf
    obtain rfl := mutualFormerChecksG_nil_inv h
    exact absurd hf (by simp)
  | cons hd rest ih =>
    intro fms h t f hf
    obtain ⟨cv, nIdx⟩ := hd
    obtain ⟨cvTa₀, cvTa, s, bs, fs, hdoor, htele, -, hrest, rfl⟩ := mutualFormerChecksG_inv h
    cases t with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      obtain rfl := hf
      refine ⟨cv, rfl, ?_⟩
      rcases checkSumTele_shape htele with ⟨rfl, -⟩ | ⟨ty, hccv⟩
      · exact hdoor.name.symm
      · exact (FrontDoorFacts.ofCheck hccv).name.symm
    | succ t =>
      simp only [List.getElem?_cons_succ] at hf ⊢
      exact ih hrest t f hf

/-- The checked formers carry the block's member names. -/
theorem mutualFormerChecksG_names {nP F : Nat} {g : Bool} {env : Env} :
    ∀ {l : List (ConstantVal × Nat)} {fms : List MutualFormerA},
      mutualFormerChecks (fueledOps mode F) env nP g l = .ok fms →
      fms.map (·.cvTa.name) = l.map (·.1.name) := by
  intro l
  induction l with
  | nil => intro fms h; obtain rfl := mutualFormerChecksG_nil_inv h; rfl
  | cons hd rest ih =>
    intro fms h
    obtain ⟨cv, nIdx⟩ := hd
    obtain ⟨cvTa₀, cvTa, s, bs, fs, hdoor, htele, -, hrest, rfl⟩ := mutualFormerChecksG_inv h
    have hname : cvTa.name = cv.name := by
      rcases checkSumTele_shape htele with ⟨rfl, -⟩ | ⟨ty, hccv⟩
      · exact hdoor.name
      · exact (FrontDoorFacts.ofCheck hccv).name
    simp only [List.map_cons, ih hrest, hname]

/-! ## The formers' conses, at a member's own name -/

/-- A lookup past the formers' conses of other names. -/
theorem consMutualFormers_find?_of_ne :
    ∀ {fms : List MutualFormerA} {env : Env} {n : Name},
      (∀ g ∈ fms, g.cvTa.name ≠ n) →
      (consMutualFormers fms env).find? n = env.find? n
  | [], _, _, _ => rfl
  | g :: gs, env, n, hne => by
    show (consMutualFormers gs ⟨.indInfo g.cvTa {} :: env.consts⟩).find? n = _
    rw [consMutualFormers_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx)),
      Env.find?_cons]
    exact if_neg (hne g List.mem_cons_self)

/-- **Every consed former is found at its own name** with the block's
empty capability record. -/
theorem consMutualFormers_find?_self :
    ∀ {fms : List MutualFormerA} {env : Env} {f : MutualFormerA},
      f ∈ fms → (fms.map (·.cvTa.name)).Nodup →
      (consMutualFormers fms env).find? f.cvTa.name = some (.indInfo f.cvTa {})
  | [], _, _, hf, _ => nomatch hf
  | g :: gs, env, f, hf, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hf with rfl | hf'
    · show (consMutualFormers gs ⟨.indInfo f.cvTa {} :: env.consts⟩).find? f.cvTa.name = _
      rw [consMutualFormers_find?_of_ne (fun x hx hh => hnd.1 (by
        rw [← hh]; exact List.mem_map_of_mem hx))]
      exact Env.find?_cons_self _ _
    · show (consMutualFormers gs ⟨.indInfo g.cvTa {} :: env.consts⟩).find? f.cvTa.name = _
      exact consMutualFormers_find?_self hf' hnd.2

/-! ## An `indInfo` found past the scratch install's later stages -/

/-- The constructors' conses add no `indInfo`. -/
theorem consMutualCtors_find?_indInfo {nP : Nat} :
    ∀ (cs : List (ConstantVal × Nat)) {env : Env} {n : Name} {cv : ConstantVal}
      {caps : IndCaps},
      (consMutualCtors nP cs env).find? n = some (.indInfo cv caps) →
      env.find? n = some (.indInfo cv caps) := by
  intro cs
  induction cs with
  | nil => intro env n cv caps h; exact h
  | cons c rest ih =>
    intro env n cv caps h
    have h' := ih h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- The recursors' store adds no `indInfo`. -/
theorem storeMutualRecs_find?_indInfo {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ (l : List (ConstantVal × Nat)) {env : Env} {n : Name} {cv : ConstantVal}
      {caps : IndCaps},
      (storeMutualRecs env₂ b fms rulesOf l env).find? n = some (.indInfo cv caps) →
      env.find? n = some (.indInfo cv caps) := by
  intro l
  induction l with
  | nil => intro env n cv caps h; exact h
  | cons hd rest ih =>
    intro env n cv caps h
    obtain ⟨cvRa, mIdx⟩ := hd
    have h' := ih h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- The projection tables add no `indInfo`. -/
theorem mutualTables_find?_indInfo {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} :
    ∀ (l : List (MutualFormerA × Nat)) {env env' : Env} {n : Name} {cv : ConstantVal}
      {caps : IndCaps},
      mutualTables (m := CheckM) b ctorsA sortss l env = .ok env' →
      env'.find? n = some (.indInfo cv caps) →
      env.find? n = some (.indInfo cv caps) := by
  intro l
  induction l with
  | nil =>
    intro env env' n cv caps h hf
    obtain rfl := mutualTables_nil_inv h
    exact hf
  | cons hd rest ih =>
    intro env env' n cv caps h hf
    obtain ⟨f, mIdx⟩ := hd
    obtain ⟨envI, hI, hrest⟩ := mutualTables_inv h
    have hfI := ih hrest hf
    rcases mutualMemberTable_inv hI with rfl | ⟨J, c, -, -, htbl⟩
    · exact hfI
    · obtain ⟨bodies, -, -, -, -, rfl⟩ := checkStructProjTable_inv htbl
      rw [Env.find?_cons] at hfI
      split at hfI
      · exact nomatch hfI
      · exact hfI

/-- **An `indInfo` at the scratch install's output was consed by the
FORMERS' stage**: everything after it is a constructor, a recursor or
a projection table. -/
theorem checkMutualCore_find?_indInfo {env envOut : Env} {b : MutualBlock} {F : Nat}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {g : Bool}
    (h : checkMutualCore (fueledOps mode F) env b streamRecs g = .ok envOut)
    {n : Name} {cv : ConstantVal} {caps : IndCaps}
    (hf : envOut.find? n = some (.indInfo cv caps)) :
    ∃ fms : List MutualFormerA,
      mutualFormers (fueledOps mode F) b.nP b.formers env g
        = .ok (consMutualFormers fms env, fms) ∧
      (consMutualFormers fms env).find? n = some (.indInfo cv caps) := by
  obtain ⟨-, -, -, -, env₁, fms, -, -, ctorsA, _sortss, -, -, -, cvRas, rulesOf,
    hformers, -, -, -, -, -, -, -, -, -, -, htables, -⟩ := checkMutualCore_inv h
  obtain ⟨-, rfl⟩ := mutualFormers_inv hformers
  refine ⟨fms, hformers, ?_⟩
  exact consMutualCtors_find?_indInfo ctorsA
    (storeMutualRecs_find?_indInfo cvRas.zipIdx
      (mutualTables_find?_indInfo fms.zipIdx htables hf))

/-- **The member records survive the scratch install**: a member's own
name answers with the constant the formers' stage checked, at the
block's empty capability record. -/
theorem checkMutualCore_member_record {env envOut : Env} {b : MutualBlock} {F : Nat}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {g : Bool}
    (h : checkMutualCore (fueledOps mode F) env b streamRecs g = .ok envOut)
    {fms : List MutualFormerA}
    (hformers : mutualFormers (fueledOps mode F) b.nP b.formers env g
      = .ok (consMutualFormers fms env, fms))
    {t : Nat} {f : MutualFormerA} (hft : fms[t]? = some f)
    {cv : ConstantVal} {caps : IndCaps}
    (hf : envOut.find? f.cvTa.name = some (.indInfo cv caps)) :
    cv = f.cvTa ∧ caps = {} := by
  obtain ⟨fms', hformers', hfind⟩ := checkMutualCore_find?_indInfo h hf
  have hfms : fms' = fms :=
    congrArg Prod.snd (Except.ok.inj (hformers'.symm.trans hformers))
  rw [hfms] at hfind
  have hnd : (fms.map (·.cvTa.name)).Nodup := by
    obtain ⟨hchecks, -⟩ := mutualFormers_inv hformers
    rw [mutualFormerChecksG_names hchecks]
    have hb : b.blockNames.Nodup := (checkMutualCore_inv h).1
    unfold MutualBlock.blockNames MutualBlock.memberNames at hb
    exact ((List.nodup_append.mp (List.nodup_append.mp hb).1).1)
  have hmem : f ∈ fms := List.mem_of_getElem? hft
  rw [consMutualFormers_find?_self hmem hnd, Option.some.injEq] at hfind
  exact ⟨(ConstantInfo.indInfo.inj hfind).1.symm, (ConstantInfo.indInfo.inj hfind).2.symm⟩

/-! ## The restored formers' environment -/

/-- **The read-back at one member**, inverted as far as the FORMER
goes: the member is the block's `mIdx`-th declared one, its index count
is the block's, and its constant and capability record are what the
scratch environment answers at its name. -/
theorem auxStored?_inv {envAux : Env} {b : MutualBlock} {mIdx : Nat} {a : AuxStored}
    (h : auxStored? envAux b mIdx = some a) :
    ∃ cv : ConstantVal, b.formers[mIdx]? = some (cv, a.nIdx) ∧
      envAux.find? cv.name = some (.indInfo a.cvTa a.caps) := by
  unfold auxStored? at h
  cases hfm : b.formers[mIdx]? with
  | none => rw [hfm] at h; exact absurd h (by simp [bind, Option.bind])
  | some p =>
    obtain ⟨cv, nIdx⟩ := p
    rw [hfm] at h
    simp only [bind, Option.bind] at h
    cases hfi : envAux.find? cv.name with
    | none => rw [hfi] at h; exact absurd h (by simp)
    | some ci =>
      rw [hfi] at h
      cases ci with
      | indInfo cvTa caps =>
        simp only [] at h
        cases hfr : envAux.find? (cv.name.str "rec") with
        | none => rw [hfr] at h; exact absurd h (by simp)
        | some cir =>
          rw [hfr] at h
          cases cir with
          | recInfo cvRa mI rP rules =>
            simp only [] at h
            split at h
            · exact absurd h (by simp)
            · simp only [pure, Option.some.injEq] at h
              obtain rfl := h
              exact ⟨cv, rfl, hfi⟩
          | _ => exact absurd h (by simp)
      | _ => exact absurd h (by simp)

/-- The restore's conses and the formers' conses agree on lists that
agree entry by entry (the capability record `{}` being the block's). -/
private theorem consNested_eq_consMutual :
    ∀ {xs : List AuxStored} {ys : List MutualFormerA} {env : Env},
      xs.length = ys.length →
      (∀ (i : Nat) (a : AuxStored) (f : MutualFormerA), xs[i]? = some a → ys[i]? = some f →
        a.cvTa = f.cvTa ∧ a.caps = {}) →
      consNestedFormers xs env = consMutualFormers ys env := by
  intro xs
  induction xs with
  | nil =>
    intro ys env hlen _
    match ys with
    | [] => rfl
    | _ :: _ => simp at hlen
  | cons a xs ih =>
    intro ys env hlen hpt
    match ys with
    | [] => simp at hlen
    | f :: ys =>
      obtain ⟨h1, h2⟩ := hpt 0 a f rfl rfl
      show consNestedFormers xs ⟨.indInfo a.cvTa a.caps :: env.consts⟩
        = consMutualFormers ys ⟨.indInfo f.cvTa {} :: env.consts⟩
      rw [h1, h2]
      exact ih (by simpa using hlen)
        (fun i a' f' ha hf => hpt (i + 1) a' f' (by simpa using ha) (by simpa using hf))

/-- **The restored formers cons the environment the SCRATCH install's
formers consed**, prefix by prefix: every record read back out of the
scratch environment is the constant the formers' stage checked, at the
block's empty capability record and its declared index count, so the
restore's `consNestedFormers` on a prefix IS `consMutualFormers` on the
same prefix of the checked formers. -/
theorem consNestedFormers_take_eq {env envOut : Env} {b : MutualBlock} {F : Nat} {g : Bool}
    {streamRecs : Option (List (ConstantVal × List RecRule))}
    (h : checkMutualCore (fueledOps mode F) env b streamRecs g = .ok envOut)
    {fms : List MutualFormerA}
    (hformers : mutualFormers (fueledOps mode F) b.nP b.formers env g
      = .ok (consMutualFormers fms env, fms))
    {stored : List AuxStored} (hst : auxStoredAll envOut b b.k = some stored)
    (k' : Nat) (hk : k' ≤ b.k) :
    consNestedFormers (stored.take k') env = consMutualFormers (fms.take k') env ∧
    ∀ (i : Nat) (a : AuxStored), i < k' → stored[i]? = some a →
      ∃ f : MutualFormerA, fms[i]? = some f ∧ a.cvTa = f.cvTa ∧ a.caps = {} ∧
        a.nIdx = f.nIdx := by
  obtain ⟨hchecks, -⟩ := mutualFormers_inv hformers
  have hlenF : fms.length = b.k := mutualFormerChecksG_length hchecks
  obtain ⟨hlenS, hall⟩ := auxStoredAll_get hst
  have key : ∀ (i : Nat) (a : AuxStored), i < b.k → stored[i]? = some a →
      ∃ f : MutualFormerA, fms[i]? = some f ∧ a.cvTa = f.cvTa ∧ a.caps = {} ∧
        a.nIdx = f.nIdx := by
    intro i a hi ha
    obtain ⟨cv, hfm, hfind⟩ := auxStored?_inv (hall i a ha)
    obtain ⟨f, hf⟩ : ∃ f : MutualFormerA, fms[i]? = some f :=
      ⟨fms[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨cv', hfm', hname⟩ := mutualFormerChecksG_nIdx hchecks i f hf
    have hp := Option.some.inj (hfm.symm.trans hfm')
    have hcv : cv = cv' := congrArg Prod.fst hp
    have hnid : a.nIdx = f.nIdx := congrArg Prod.snd hp
    rw [hcv, hname] at hfind
    obtain ⟨hcvTa, hcaps⟩ := checkMutualCore_member_record h hformers hf hfind
    exact ⟨f, hf, hcvTa, hcaps, hnid⟩
  refine ⟨?_, fun i a hi ha => key i a (by omega) ha⟩
  refine consNested_eq_consMutual ?_ ?_
  · rw [List.length_take, List.length_take, hlenS, hlenF]
  · intro i a f ha hf
    rw [List.getElem?_take] at ha hf
    by_cases hik : i < k'
    · rw [if_pos hik] at ha hf
      obtain ⟨f', hf', h1, h2, -⟩ := key i a (by omega) ha
      rw [hf'] at hf
      obtain rfl := Option.some.inj hf
      exact ⟨h1, h2⟩
    · rw [if_neg hik] at ha
      exact absurd ha (by simp)

/-! ## The constructors' conses, at a constructor's own name -/

/-- A lookup past the constructors' conses of other names. -/
private theorem consMutualCtors_find?_of_ne {nP : Nat} :
    ∀ {cs : List (ConstantVal × Nat)} {env : Env} {n : Name},
      (∀ c ∈ cs, c.1.name ≠ n) →
      (consMutualCtors nP cs env).find? n = env.find? n
  | [], _, _, _ => rfl
  | c :: cs, env, n, hne => by
    show (consMutualCtors nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩).find? n = _
    rw [consMutualCtors_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx)),
      Env.find?_cons]
    exact if_neg (hne c List.mem_cons_self)

/-- **Every consed constructor is found at its own name**, with the
block's parameter count and its own field count. -/
theorem consMutualCtors_find?_self {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env} {J : Nat} {cA : ConstantVal × Nat},
      (ctorsA.map (·.1.name)).Nodup → ctorsA[J]? = some cA →
      (consMutualCtors nP ctorsA env).find? cA.1.name = some (.ctorInfo cA.1 nP cA.2)
  | [], _, _, _, _, hJ => absurd hJ (by simp)
  | c :: cs, env, J, cA, hnd, hJ => by
    rw [List.map_cons, List.nodup_cons] at hnd
    cases J with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hJ
      obtain rfl := hJ
      show (consMutualCtors nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩).find? c.1.name = _
      rw [consMutualCtors_find?_of_ne (fun x hx hh => hnd.1 (by
        rw [← hh]; exact List.mem_map_of_mem hx))]
      exact Env.find?_cons_self _ _
    | succ J =>
      simp only [List.getElem?_cons_succ] at hJ
      show (consMutualCtors nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩).find? cA.1.name = _
      exact consMutualCtors_find?_self hnd.2 hJ

/-! ## A `ctorInfo` through the scratch install's later stages -/

/-- A cons at another name keeps a successful lookup. -/
private theorem find?_cons_of_ne {c : ConstantInfo} {env : Env} {n : Name} {ci : ConstantInfo}
    (hne : c.name ≠ n) (h : env.find? n = some ci) :
    Env.find? ⟨c :: env.consts⟩ n = some ci := by
  rw [Env.find?_cons, if_neg hne]
  exact h

/-- The recursors' store keeps a `ctorInfo` answer at every name it
does not cons itself. -/
theorem storeMutualRecs_find?_ctorInfo {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ (l : List (ConstantVal × Nat)) {env : Env} {n : Name} {cv : ConstantVal} {nP nF : Nat},
      (∀ p ∈ l, p.1.name ≠ n) →
      env.find? n = some (.ctorInfo cv nP nF) →
      (storeMutualRecs env₂ b fms rulesOf l env).find? n = some (.ctorInfo cv nP nF) := by
  intro l
  induction l with
  | nil => intro env n cv nP nF _ hf; exact hf
  | cons hd rest ih =>
    intro env n cv nP nF hne hf
    obtain ⟨cvRa, mIdx⟩ := hd
    exact ih (fun p hp => hne p (List.mem_cons_of_mem _ hp))
      (find?_cons_of_ne (hne (cvRa, mIdx) List.mem_cons_self) hf)

/-- The projection tables keep a `ctorInfo` answer: a table is consed
at a name the stage's own guard found free. -/
theorem mutualTables_find?_ctorInfo {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} :
    ∀ (l : List (MutualFormerA × Nat)) {env env' : Env} {n : Name} {cv : ConstantVal}
      {nP nF : Nat},
      mutualTables (m := CheckM) b ctorsA sortss l env = .ok env' →
      env.find? n = some (.ctorInfo cv nP nF) →
      env'.find? n = some (.ctorInfo cv nP nF) := by
  intro l
  induction l with
  | nil =>
    intro env env' n cv nP nF h hf
    obtain rfl := mutualTables_nil_inv h
    exact hf
  | cons hd rest ih =>
    intro env env' n cv nP nF h hf
    obtain ⟨f, mIdx⟩ := hd
    obtain ⟨envI, hI, hrest⟩ := mutualTables_inv h
    refine ih hrest ?_
    rcases mutualMemberTable_inv hI with rfl | ⟨J, c, -, -, htbl⟩
    · exact hf
    · obtain ⟨bodies, -, -, -, hfresh, rfl⟩ := checkStructProjTable_inv htbl
      exact Env.find?_cons_of_fresh hfresh hf

/-! ## The constructors' stage, at two grades of `isProp` -/

/-- A thrown step never succeeds. -/
private theorem auxThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact auxThrow_ne_ok (by assumption))
        | (exfalso; exact auxThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-- **What one constructor's stage STORES**: the door's constant, run
through the positivity normalisation — neither step reads `isProp`,
which enters only at the fields' sorts. -/
private theorem checkMutualCtorG_stored {env : Env} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal} {nF F : Nat} {g : Bool} {sorts : List Level}
    (h : checkMutualCtor (fueledOps mode F) env memberNames T lps nP nIdx resSort isProp large
      cvC nF cvTa g = .ok (cvCa, sorts)) :
    ∃ cvCa₀ : ConstantVal,
      (if g then checkConstantValPre (m := CheckM) (fueledOps mode F) env cvC
        else checkConstantVal (fueledOps mode F) env cvC) = .ok cvCa₀ ∧
      normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa₀ g
        = .ok cvCa := by
  unfold checkMutualCtor at h
  cases g <;> simp only [if_true, Bool.false_eq_true, if_false] at h ⊢
  all_goals
  obtain ⟨cvCa₀, hccv₀, h⟩ := exceptBind_ok h
  obtain ⟨cvCa', hnorm, h⟩ := exceptBind_ok h
  obtain ⟨q, -, h⟩ := exceptBind_ok h
  obtain ⟨cbs, cbody⟩ := q
  try simp only at h
  by_cases hc : structCtorResidOk T lps nP nF nIdx cbody = true
  case neg => rw [if_neg hc] at h; close_throw
  rw [if_pos hc] at h
  obtain ⟨cq, -, h⟩ := exceptBind_ok h
  obtain ⟨fvsP, crest⟩ := cq
  obtain ⟨tq, -, h⟩ := exceptBind_ok h
  obtain ⟨tfvs, trest⟩ := tq
  try simp only at h
  obtain ⟨u, -, h⟩ := exceptBind_ok h
  obtain ⟨xq, -, h⟩ := exceptBind_ok h
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
  obtain ⟨sorts', -, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨cvCa₀, hccv₀, hnorm⟩

/-- The constructors' stage stores the same constants at every
`isProp`: both runs go through the same door and the same
normalisation. -/
private theorem checkMutualCtorsG_ctorsA_det {env : Env} {b : MutualBlock}
    {fms : List MutualFormerA} {isProp₁ isProp₂ g : Bool} {F : Nat} {cs : List MutualCtor}
    {ctorsA₁ ctorsA₂ : List (ConstantVal × Nat)} {sortss₁ sortss₂ : List (List Level)}
    (h₁ : checkMutualCtors (fueledOps mode F) env b fms isProp₁ g cs = .ok (ctorsA₁, sortss₁))
    (h₂ : checkMutualCtors (fueledOps mode F) env b fms isProp₂ g cs = .ok (ctorsA₂, sortss₂)) :
    ctorsA₁ = ctorsA₂ := by
  obtain ⟨hlen₁, -, hall₁⟩ := checkMutualCtors_inv h₁
  obtain ⟨hlen₂, -, hall₂⟩ := checkMutualCtors_inv h₂
  refine List.ext_getElem? fun J => ?_
  cases hJ₁ : ctorsA₁[J]? with
  | none =>
    have hn : ctorsA₂[J]? = none := by
      rw [List.getElem?_eq_none_iff] at hJ₁ ⊢; omega
    rw [hn]
  | some cA₁ =>
    have hJl : J < cs.length := by
      have := (List.getElem?_eq_some_iff.mp hJ₁).1
      omega
    obtain ⟨c, hc⟩ : ∃ c, cs[J]? = some c := ⟨cs[J]'hJl, List.getElem?_eq_getElem hJl⟩
    obtain ⟨cA₂, hJ₂⟩ : ∃ cA₂, ctorsA₂[J]? = some cA₂ :=
      ⟨ctorsA₂[J]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hnF₁, s₁, -, hrun₁⟩ := hall₁ J c cA₁ hc hJ₁
    obtain ⟨hnF₂, s₂, -, hrun₂⟩ := hall₂ J c cA₂ hc hJ₂
    obtain ⟨cvCa₀₁, hd₁, hn₁⟩ := checkMutualCtorG_stored hrun₁
    obtain ⟨cvCa₀₂, hd₂, hn₂⟩ := checkMutualCtorG_stored hrun₂
    obtain rfl : cvCa₀₂ = cvCa₀₁ := Except.ok.inj (hd₂.symm.trans hd₁)
    have hfst : cA₁.1 = cA₂.1 := Except.ok.inj (hn₁.symm.trans hn₂)
    rw [hJ₂]
    have : cA₁ = cA₂ := by
      obtain ⟨a₁, b₁⟩ := cA₁
      obtain ⟨a₂, b₂⟩ := cA₂
      simp only at hfst hnF₁ hnF₂
      rw [hfst, hnF₁, hnF₂]
    rw [this]

/-- **The checked constructors' names are the block record's**
(`checkMutualCtors`' constant check keeps the name). -/
private theorem ctorsA_names_eq {env : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {isProp g : Bool} {F : Nat} {cs : List MutualCtor} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)}
    (h : checkMutualCtors (fueledOps mode F) env b fms isProp g cs = .ok (ctorsA, sortss)) :
    ctorsA.map (·.1.name) = cs.map (·.cv.name) := by
  obtain ⟨hlen, -, hall⟩ := checkMutualCtors_inv h
  refine List.ext_getElem? fun J => ?_
  rw [List.getElem?_map, List.getElem?_map]
  cases hJ : ctorsA[J]? with
  | none =>
    have hn : cs[J]? = none := by
      rw [List.getElem?_eq_none_iff] at hJ ⊢; omega
    rw [hn]
    rfl
  | some cA =>
    have hJl : J < cs.length := by
      have := (List.getElem?_eq_some_iff.mp hJ).1
      omega
    obtain ⟨c, hc⟩ : ∃ c, cs[J]? = some c := ⟨cs[J]'hJl, List.getElem?_eq_getElem hJl⟩
    obtain ⟨-, sorts, -, hrun⟩ := hall J c cA hc hJ
    obtain ⟨⟨ty', hccv⟩, -, -⟩ := checkMutualCtorG_shape hrun
    rw [hc]
    simp only [Option.map_some, Option.some.injEq]
    exact hccv.name

/-- **The constructors' records survive the scratch install**: the
constructors' conses answer at every checked constructor's own name,
and neither the recursors' group (the block's `Nodup` keeps the
recursor names off the constructors') nor the projection tables (each
consed at a name its own guard found free) touches that answer. -/
theorem checkMutualCore_ctor_record {env envOut : Env} {b : MutualBlock} {F : Nat}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {g : Bool}
    (h : checkMutualCore (fueledOps mode F) env b streamRecs g = .ok envOut)
    {fms : List MutualFormerA}
    (hformers : mutualFormers (fueledOps mode F) b.nP b.formers env g
      = .ok (consMutualFormers fms env, fms))
    {isProp : Bool} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hctors : checkMutualCtors (fueledOps mode F) (consMutualFormers fms env) b fms isProp g
      b.ctors = .ok (ctorsA, sortss))
    {J : Nat} {cA : ConstantVal × Nat} (hJ : ctorsA[J]? = some cA) :
    envOut.find? cA.1.name = some (.ctorInfo cA.1 b.nP cA.2) := by
  obtain ⟨hnd, -, -, -, env₁, fms', f₀, -, ctorsA', sortss', -, formers4, ctors4, cvRas,
    rulesOf, hformers', -, -, -, -, hctors', -, -, -, hrectys, -, htables, -⟩ :=
    checkMutualCore_inv h
  obtain ⟨-, rfl⟩ := mutualFormers_inv hformers'
  obtain rfl : fms = fms' := congrArg Prod.snd (Except.ok.inj (hformers.symm.trans hformers'))
  obtain rfl : ctorsA = ctorsA' := checkMutualCtorsG_ctorsA_det hctors hctors'
  -- the constructors' names are the block record's, and the block's
  -- `Nodup` says they are distinct and none of them is a recursor's
  have hnames : ctorsA.map (·.1.name) = b.ctors.map (·.cv.name) := ctorsA_names_eq hctors
  unfold MutualBlock.blockNames MutualBlock.memberNames at hnd
  have hndC : (ctorsA.map (·.1.name)).Nodup := by
    rw [hnames]
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  have hmemC : cA.1.name ∈ b.ctors.map (·.cv.name) := by
    rw [← hnames]
    exact List.mem_map_of_mem (List.mem_of_getElem? hJ)
  have hneRec : ∀ r ∈ (List.range b.k).map b.recName, cA.1.name ≠ r := fun r hr =>
    (List.nodup_append.mp hnd).2.2 cA.1.name (List.mem_append_right _ hmemC) r hr
  have hne : ∀ p ∈ cvRas.zipIdx, p.1.name ≠ cA.1.name := by
    intro p hp hpn
    obtain ⟨cvRa, mIdx⟩ := p
    have hget : cvRas[mIdx]? = some cvRa := List.mk_mem_zipIdx_iff_getElem?.mp hp
    obtain ⟨hlenR, hallR⟩ := checkMutualRecTys_inv hrectys
    have hlt : mIdx < b.k := by
      have hm := (List.getElem?_eq_some_iff.mp hget).1
      rw [hlenR] at hm
      exact hm
    obtain ⟨cvRa', hget', hrec⟩ := hallR mIdx hlt
    obtain rfl := Option.some.inj (hget.symm.trans hget')
    obtain ⟨recTy, -, -, -, -, -, -, -, -, -, -, rfl⟩ := checkMutualRecTy_shape hrec
    exact hneRec (b.recName mIdx) (List.mem_map_of_mem (List.mem_range.mpr hlt)) hpn.symm
  exact mutualTables_find?_ctorInfo fms.zipIdx htables
    (storeMutualRecs_find?_ctorInfo cvRas.zipIdx hne (consMutualCtors_find?_self hndC hJ))

/-! ## The read-back at one member's CONSTRUCTORS -/

/-- An `Option`-`mapM` keeps its list's length (`NestedElimInv`'s
`mapM_option_length`, re-proved here: this module does not import it). -/
private theorem mapM_option_len {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨b, -, bs, hbs, rfl⟩ := h
    simp [mapM_option_len hbs]

/-- **The read-back at one member's constructors**: as many as the
member owns, each the `ctorInfo` the scratch environment answers at the
declared constructor's own name. -/
theorem auxStored?_ctors {envAux : Env} {b : MutualBlock} {mIdx : Nat} {a : AuxStored}
    (h : auxStored? envAux b mIdx = some a) :
    a.ctors.length = (b.ownCtors mIdx).length ∧
    ∀ (j : Nat) (c : ConstantVal × Nat × Nat), a.ctors[j]? = some c →
      ∃ (J : Nat) (mc : MutualCtor), (b.ownCtors mIdx)[j]? = some (J, mc) ∧
        envAux.find? mc.cv.name = some (.ctorInfo c.1 c.2.1 c.2.2) := by
  unfold auxStored? at h
  cases hfm : b.formers[mIdx]? with
  | none => rw [hfm] at h; exact absurd h (by simp [bind, Option.bind])
  | some p =>
    obtain ⟨cv, nIdx⟩ := p
    rw [hfm] at h
    simp only [bind, Option.bind] at h
    cases hfi : envAux.find? cv.name with
    | none => rw [hfi] at h; exact absurd h (by simp)
    | some ci =>
      rw [hfi] at h
      cases ci with
      | indInfo cvTa caps =>
        simp only [] at h
        cases hfr : envAux.find? (cv.name.str "rec") with
        | none => rw [hfr] at h; exact absurd h (by simp)
        | some cir =>
          rw [hfr] at h
          cases cir with
          | recInfo cvRa mI rP rules =>
            simp only [] at h
            split at h
            · exact absurd h (by simp)
            · next ctors hm =>
              simp only [pure, Option.some.injEq] at h
              obtain rfl := h
              refine ⟨mapM_option_len hm, fun j c hc => ?_⟩
              have hj : j < (b.ownCtors mIdx).length := by
                have hjc := (List.getElem?_eq_some_iff.mp hc).1
                rw [mapM_option_len hm] at hjc
                exact hjc
              obtain ⟨q, hq⟩ : ∃ q, (b.ownCtors mIdx)[j]? = some q :=
                ⟨(b.ownCtors mIdx)[j]'hj, List.getElem?_eq_getElem hj⟩
              obtain ⟨J, mc⟩ := q
              obtain ⟨c', hc', hf⟩ := mapM_option_inv hm j (J, mc) hq
              obtain rfl := Option.some.inj (hc.symm.trans hc')
              refine ⟨J, mc, hq, ?_⟩
              simp only [] at hf
              cases hfc : envAux.find? mc.cv.name with
              | none => rw [hfc] at hf; exact absurd hf (by simp)
              | some cic =>
                rw [hfc] at hf
                cases cic with
                | ctorInfo cvCa nPc nFc =>
                  simp only [pure, Option.some.injEq] at hf
                  obtain rfl := hf
                  rfl
                | _ => exact absurd hf (by simp)
          | _ => exact absurd h (by simp)
      | _ => exact absurd h (by simp)

/-! ## The restored constructors, against the stage's -/

/-- **THE READ-BACK AT THE CONSTRUCTORS** (task #315 M6 s6): member
`mm`'s stored constructors are the constructors' stage's own run of
`b.ctors`, positionally — the member owns as many as the block groups
under it, and the `j`-th of them is the checked constructor at the
block's global index `b.ownOffset mm + j`, with the block's parameter
count and that constructor's field count.

The chain: the read-back inverts to the scratch environment's
`ctorInfo` at the DECLARED constructor's name
(`auxStored?_ctors`), the grouping guard places that constructor at
`b.ownOffset mm + j` (`ownCtors_getElem?_idx`), and the install's own
record at that name is the checked constructor
(`checkMutualCore_ctor_record`); the two answers are one. -/
theorem auxStored_ctor_eq {env envAux : Env} {b : MutualBlock} {F : Nat}
    (h : checkMutualCore (fueledOps mode F) env b none true = .ok envAux)
    {fms : List MutualFormerA}
    (hformers : mutualFormers (fueledOps mode F) b.nP b.formers env true
      = .ok (consMutualFormers fms env, fms))
    {isProp : Bool} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hctors : checkMutualCtors (fueledOps mode F) (consMutualFormers fms env) b fms isProp true
      b.ctors = .ok (ctorsA, sortss))
    (hg : mutualCtorsGrouped b.ctors = true)
    {stored : List AuxStored} (hst : auxStoredAll envAux b b.k = some stored)
    {mm : Nat} {a : AuxStored} (ha : stored[mm]? = some a) :
    a.ctors.length = (b.ownCtors mm).length ∧
    ∀ (j : Nat) (c : ConstantVal × Nat × Nat), a.ctors[j]? = some c →
      ∃ cA : ConstantVal × Nat, ctorsA[b.ownOffset mm + j]? = some cA ∧
        c.1 = cA.1 ∧ c.2.1 = b.nP ∧ c.2.2 = cA.2 := by
  obtain ⟨-, hall⟩ := auxStoredAll_get hst
  obtain ⟨hlenA, hallA⟩ := auxStored?_ctors (hall mm a ha)
  refine ⟨hlenA, fun j c hc => ?_⟩
  obtain ⟨J, mc, hown, hfind⟩ := hallA j c hc
  obtain ⟨hct, -⟩ := ownCtors_getElem?_ctors hown
  obtain ⟨hlenC, -, hallC⟩ := checkMutualCtors_inv hctors
  obtain ⟨cA, hcA⟩ : ∃ cA, ctorsA[J]? = some cA := by
    have hJl : J < ctorsA.length := by
      have hJc := (List.getElem?_eq_some_iff.mp hct).1
      rw [← hlenC] at hJc
      exact hJc
    exact ⟨ctorsA[J]'hJl, List.getElem?_eq_getElem hJl⟩
  obtain ⟨-, sorts, -, hrun⟩ := hallC J mc cA hct hcA
  obtain ⟨⟨ty', hccv⟩, -, -⟩ := checkMutualCtorG_shape hrun
  have hrec := checkMutualCore_ctor_record h hformers hctors hcA
  rw [hccv.name] at hrec
  obtain ⟨e1, e2, e3⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfind.symm.trans hrec))
  exact ⟨cA, by rw [← ownCtors_getElem?_idx hg hown]; exact hcA, e1, e2, e3⟩

/-! ## The restored constructors' names (task #315 M6 s8)

The restore keeps the block's parameter count on every constructor and
keeps the names DISTINCT: member `mm`'s `j`-th restored constructor
carries the name of `ctorsA[b.ownOffset mm + j]`, the grouping guard
makes `(mm, j) ↦ b.ownOffset mm + j` injective on the members' runs,
and the block's `Nodup` names the auxiliary constructors apart. -/

private theorem restoredCtors_offset_le_add (b : MutualBlock) (m : Nat) :
    ∀ d, b.ownOffset m ≤ b.ownOffset (m + d)
  | 0 => Nat.le_refl _
  | d + 1 => by
    rw [show m + (d + 1) = (m + d) + 1 from rfl, ownOffset_succ]
    exact Nat.le_trans (restoredCtors_offset_le_add b m d) (Nat.le_add_right _ _)

private theorem restoredCtors_offset_mono {b : MutualBlock} {m n : Nat} (h : m ≤ n) :
    b.ownOffset m ≤ b.ownOffset n := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  rw [← hd]
  exact restoredCtors_offset_le_add b m d

private theorem restoredCtors_nodup_idx {γ : Type} {N : List γ} (hN : N.Nodup) {a c : Nat} {x : γ}
    (ha : N[a]? = some x) (hc : N[c]? = some x) : a = c := by
  obtain ⟨hal, hax⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hcl, hcx⟩ := List.getElem?_eq_some_iff.mp hc
  rcases Nat.lt_trichotomy a c with h | h | h
  · exact absurd (hax.trans hcx.symm)
      ((List.pairwise_iff_getElem (R := fun x y => x ≠ y)).mp hN a c hal hcl h)
  · exact h
  · exact absurd (hcx.trans hax.symm)
      ((List.pairwise_iff_getElem (R := fun x y => x ≠ y)).mp hN c a hcl hal h)

private theorem restoredCtors_at {env envAux envR : Env} {p : NestedParts} {b : MutualBlock}
    {F : Nat} {fms : List MutualFormerA} {isProp : Bool} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {R : RestoreTbl} {lps : List Name}
    (haux : checkMutualCore (fueledOps mode F) env b none true = .ok envAux)
    (hformers : mutualFormers (fueledOps mode F) b.nP b.formers env true
      = .ok (consMutualFormers fms env, fms))
    (hctorsA : checkMutualCtors (fueledOps mode F) (consMutualFormers fms env) b fms isProp true
      b.ctors = .ok (ctorsA, sortss))
    (h3 : mutualCtorsGrouped b.ctors = true)
    (hstored : auxStoredAll envAux b b.k = some stored)
    (hctors : (stored.take p.k).mapM
      (fun a => restoreCtors (m := CheckM) (fueledOps mode F) envR R lps a.ctors) = .ok ctorsR) :
    ∀ (mm j : Nat) (l : List (ConstantVal × Nat × Nat)) (c : ConstantVal × Nat × Nat),
      ctorsR[mm]? = some l → l[j]? = some c →
        c.2.1 = b.nP ∧ j < (b.ownCtors mm).length ∧
        ∃ cA : ConstantVal × Nat,
          ctorsA[b.ownOffset mm + j]? = some cA ∧ c.1.name = cA.1.name := by
  obtain ⟨hlenR, hallR⟩ := mapM_except_inv hctors
  intro mm j l c hl hc
  have hmm : mm < (stored.take p.k).length := by
    rw [← hlenR]; exact (List.getElem?_eq_some_iff.mp hl).1
  obtain ⟨a, l', ha, hl', hrun⟩ := hallR mm hmm
  obtain rfl := Option.some.inj (hl'.symm.trans hl)
  have hst : stored[mm]? = some a := by
    rw [List.getElem?_take] at ha
    by_cases hlt : mm < p.k
    · rwa [if_pos hlt] at ha
    · rw [if_neg hlt] at ha; exact absurd ha (by simp)
  obtain ⟨hlenC, hallC⟩ := restoreCtors_id hrun
  have hj : j < a.ctors.length := by
    rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, a.ctors[j]? = some c₀ := ⟨a.ctors[j]'hj, List.getElem?_eq_getElem hj⟩
  obtain ⟨ty, -, hceq⟩ := hallC j c₀ c hc₀ hc
  obtain ⟨hlenOwn, hallOwn⟩ := auxStored_ctor_eq haux hformers hctorsA h3 hstored hst
  obtain ⟨cA, hcA, e1, e2, -⟩ := hallOwn j c₀ hc₀
  refine ⟨?_, ?_, cA, hcA, ?_⟩
  · rw [hceq]; exact e2
  · rw [← hlenOwn]; exact hj
  · rw [hceq]
    change c₀.1.name = cA.1.name
    exact congrArg ConstantVal.name e1

/-- The restored constructors carry the block's parameter count. -/
theorem restoredCtors_nP {env envAux envR : Env} {p : NestedParts} {b : MutualBlock} {F : Nat}
    {fms : List MutualFormerA} {isProp : Bool} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {R : RestoreTbl} {lps : List Name}
    (haux : checkMutualCore (fueledOps mode F) env b none true = .ok envAux)
    (hformers : mutualFormers (fueledOps mode F) b.nP b.formers env true
      = .ok (consMutualFormers fms env, fms))
    (hctorsA : checkMutualCtors (fueledOps mode F) (consMutualFormers fms env) b fms isProp true
      b.ctors = .ok (ctorsA, sortss))
    (h3 : mutualCtorsGrouped b.ctors = true)
    (hstored : auxStoredAll envAux b b.k = some stored)
    (hctors : (stored.take p.k).mapM
      (fun a => restoreCtors (m := CheckM) (fueledOps mode F) envR R lps a.ctors) = .ok ctorsR) :
    ∀ c ∈ ctorsR.flatten, c.2.1 = b.nP := by
  have hkey := restoredCtors_at haux hformers hctorsA h3 hstored hctors
  intro c hc
  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
  obtain ⟨mm, hmm⟩ := List.getElem?_of_mem hl
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hcl
  exact (hkey mm j l c hmm hj).1

/-- **THE RUN-FREE CORE** (task #315 M8): the flattened restored
constructors' names are pairwise distinct as soon as the POSITIONAL
KEY holds — position `(mm, j)` of `ctorsR` carries the name that sits
at `ownOffset mm + j` of a `Nodup` name list.  Whatever produced
`ctorsR` is irrelevant: the pure route reads the key off its runs
(`restoredCtors_at`), the cached mirror off the read-back's skeleton
(`auxStoredAll_ctor_name`), and both land here. -/
theorem restoredCtors_nodup_of_key {b : MutualBlock} {N : List Name} (hndA : N.Nodup)
    {ctorsR : List (List (ConstantVal × Nat × Nat))}
    (hidx : ∀ (mm j : Nat) (l : List (ConstantVal × Nat × Nat)) (c : ConstantVal × Nat × Nat),
      ctorsR[mm]? = some l → l[j]? = some c →
        j < (b.ownCtors mm).length ∧ N[b.ownOffset mm + j]? = some c.1.name) :
    (ctorsR.flatten.map (·.1.name)).Nodup := by
  rw [List.map_flatten]
  refine List.pairwise_flatten.mpr ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨lr, hlr, rfl⟩ := List.mem_map.mp hl
    obtain ⟨mm, hmm⟩ := List.getElem?_of_mem hlr
    refine List.pairwise_map.mpr (List.pairwise_iff_getElem.mpr ?_)
    intro i j hi hj hij hEq
    obtain ⟨-, h1⟩ := hidx mm i lr lr[i] hmm (List.getElem?_eq_getElem hi)
    obtain ⟨-, h2⟩ := hidx mm j lr lr[j] hmm (List.getElem?_eq_getElem hj)
    rw [hEq] at h1
    have := restoredCtors_nodup_idx hndA h1 h2
    omega
  · refine List.pairwise_map.mpr (List.pairwise_iff_getElem.mpr ?_)
    intro i j hi hj hij x hx y hy hEq
    obtain ⟨cx, hcx, rfl⟩ := List.mem_map.mp hx
    obtain ⟨cy, hcy, rfl⟩ := List.mem_map.mp hy
    obtain ⟨jx, hjx⟩ := List.getElem?_of_mem hcx
    obtain ⟨jy, hjy⟩ := List.getElem?_of_mem hcy
    obtain ⟨hbx, h1⟩ := hidx i jx _ cx (List.getElem?_eq_getElem hi) hjx
    obtain ⟨-, h2⟩ := hidx j jy _ cy (List.getElem?_eq_getElem hj) hjy
    rw [hEq] at h1
    have heq2 := restoredCtors_nodup_idx hndA h1 h2
    have hmono : b.ownOffset (i + 1) ≤ b.ownOffset j := restoredCtors_offset_mono hij
    rw [ownOffset_succ] at hmono
    omega


/-- **The restored constructors' names are pairwise distinct**. -/
theorem restoredCtors_nodup {env envAux envR : Env} {p : NestedParts} {b : MutualBlock} {F : Nat}
    {fms : List MutualFormerA} {isProp : Bool} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {R : RestoreTbl} {lps : List Name}
    (haux : checkMutualCore (fueledOps mode F) env b none true = .ok envAux)
    (hformers : mutualFormers (fueledOps mode F) b.nP b.formers env true
      = .ok (consMutualFormers fms env, fms))
    (hctorsA : checkMutualCtors (fueledOps mode F) (consMutualFormers fms env) b fms isProp true
      b.ctors = .ok (ctorsA, sortss))
    (h3 : mutualCtorsGrouped b.ctors = true)
    (hstored : auxStoredAll envAux b b.k = some stored)
    (hctors : (stored.take p.k).mapM
      (fun a => restoreCtors (m := CheckM) (fueledOps mode F) envR R lps a.ctors) = .ok ctorsR)
    (hndB : b.blockNames.Nodup)
    (hnamesC : ctorsA.map (·.1.name) = b.ctors.map (·.cv.name)) :
    (ctorsR.flatten.map (·.1.name)).Nodup := by
  have hkey := restoredCtors_at haux hformers hctorsA h3 hstored hctors
  have hndA : (ctorsA.map (·.1.name)).Nodup := by
    have hb : (b.memberNames ++ b.ctors.map (·.cv.name)
        ++ (List.range b.k).map b.recName).Nodup := hndB
    rw [hnamesC]
    exact (List.nodup_append.mp (List.nodup_append.mp hb).1).2.1
  have hidx : ∀ (mm j : Nat) (l : List (ConstantVal × Nat × Nat)) (c : ConstantVal × Nat × Nat),
      ctorsR[mm]? = some l → l[j]? = some c →
        j < (b.ownCtors mm).length ∧
        (ctorsA.map (·.1.name))[b.ownOffset mm + j]? = some c.1.name := by
    intro mm j l c hl hc
    obtain ⟨-, hjl, cA, hcA, hn⟩ := hkey mm j l c hl hc
    refine ⟨hjl, ?_⟩
    rw [List.getElem?_map, hcA, hn]
    rfl
  exact restoredCtors_nodup_of_key hndA hidx
end ConLeche
