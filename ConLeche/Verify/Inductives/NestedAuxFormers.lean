module

public import ConLeche.Kernel.Inductives.NestedInstall
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedElimInv

public section

/-!
# The auxiliary block, read at its three seams (task #315 M6 s9)

Three readings of the scratch install's INPUT — the auxiliary block and
the pins the elimination minted — that the model tier's ψ consumes and
no stored record exposes.

* **The formers' stage stores the DECLARED constant**
  (`mutualFormerChecksTrue_at`): at the auxiliary route (`g = true`)
  the front door is `checkConstantValPre`, which returns its input, and
  the telescope stage (`checkSumTele`) takes its first arm at a type
  that already IS a syntactic telescope ending in a sort — so what the
  stage stores is the constant the elimination minted, syntactically.
  The copies' types are built as `Π p⃗, J's type at the pins`, so the
  telescope premise is discharged at the mint.
* **A container's group is one group** (`nestedContainersOk_group`):
  K.14's Bool records that every member of a pinned container's
  `all`-group recovers the same parameter count and the same member
  names, and that the pins are structurally distinct.
* **A member's own constructors are its own type's**
  (`auxBlock_ownCtors_length`): `auxBlock` flattens the elimination's
  types tagging each constructor with its type's index, so the
  `ownCtors` selection at `mIdx` counts exactly the `mIdx`-th type's
  constructors — the group indices are distinct across groups, so no
  other type contributes.
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## The formers' stage at the auxiliary route -/

/-- The formers' loop at a grade, one member, keeping the DOOR'S RUN
(`mutualFormerChecksG_inv` keeps its facts instead, which no longer
says WHICH door ran). -/
private theorem formerChecksG_cons_run {nP F nIdx : Nat} {g : Bool} {cv : ConstantVal}
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

/-- **The telescope stage at a type that already IS a telescope**: the
first arm of `checkSumTele`, which returns its input and the result
sort — nothing is reduced and nothing is re-checked. -/
private theorem checkSumTele_strip {env : Env} {cv cvTa₀ : ConstantVal} {n F : Nat}
    {bs : List (Expr × BinderMeta)} {u : Level}
    (hstrip : cvTa₀.type.stripPis n = some (bs, Expr.sort u)) :
    checkSumTele (m := CheckM) (fueledOps mode F) env cv n cvTa₀ = .ok (cvTa₀, u) := by
  unfold checkSumTele
  rw [hstrip]
  rfl

/-- **THE FORMERS' STAGE AT THE AUXILIARY ROUTE STORES THE DECLARED
CONSTANT** (task #315 M6 s9): at `g = true` the front door is
`checkConstantValPre`, whose output IS its input
(`checkConstantValPre_ok`), and `checkSumTele` takes its first arm
whenever the declared type is a syntactic telescope of the member's
parameters and indices ending in a sort (`checkSumTele_strip`).  So the
`t`-th checked former is the `t`-th declared member, with its declared
index count and — under that telescope premise, which the elimination's
mint discharges by construction — its declared constant unchanged. -/
theorem mutualFormerChecksTrue_at {nP F : Nat} {env : Env} :
    ∀ {l : List (ConstantVal × Nat)} {fms : List MutualFormerA},
      mutualFormerChecks (fueledOps mode F) env nP true l = .ok fms →
      ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
        ∃ (cv : ConstantVal) (nIdx : Nat), l[t]? = some (cv, nIdx) ∧ f.nIdx = nIdx ∧
          ((∃ (bs : List (Expr × BinderMeta)) (u : Level),
              cv.type.stripPis (nP + nIdx) = some (bs, .sort u)) →
            f.cvTa = cv) := by
  intro l
  induction l with
  | nil =>
    intro fms h t f hf
    obtain rfl := mutualFormerChecksG_nil_inv h
    exact absurd hf (by simp)
  | cons hd rest ih =>
    intro fms h t f hf
    obtain ⟨cv, nIdx⟩ := hd
    obtain ⟨cvTa₀, cvTa, s, bs, fs, hdoor, htele, -, hrest, rfl⟩ := formerChecksG_cons_run h
    cases t with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      obtain rfl := hf
      refine ⟨cv, nIdx, rfl, rfl, ?_⟩
      rintro ⟨bs', u, hs⟩
      simp only [if_true] at hdoor
      have hcv : cvTa₀ = cv := checkConstantValPre_ok hdoor
      rw [hcv, checkSumTele_strip hs] at htele
      simp only [Except.ok.injEq, Prod.mk.injEq] at htele
      exact htele.1.symm
    | succ t =>
      simp only [List.getElem?_cons_succ] at hf ⊢
      exact ih hrest t f hf

/-! ## The pinned containers' groups -/

/-- **THE CONTAINER'S CONSTRUCTOR NAMES ROUND-TRIP** (task #315 K.53,
lane M7-2's request), inverted: at every pin, every constructor of the
container's own member survives the mint's rename and the restore's
rename back.  `NestedCtorPinNames` is this, at a positional pin. -/
theorem nestedContainersOk_ctorNames {env : Env} {pins : List NestedPin}
    (h : nestedContainersOk env pins = true) :
    ∀ q ∈ pins, ∀ (ci : ContainerInfo) (J : ContainerMember),
      containerInfo? env q.container = some ci → J ∈ ci.members → J.name = q.container →
      ∀ cc ∈ J.ctors,
        Name.replacePrefix q.aux q.container
          (Name.replacePrefix J.name q.aux cc.name) = cc.name := by
  simp only [nestedContainersOk, Bool.and_eq_true] at h
  intro q hq ci J hci hJ hJn cc hcc
  have hq' := List.all_eq_true.mp h.2 q hq
  rw [hci] at hq'
  simp only [Bool.and_eq_true] at hq'
  have hJ' := List.all_eq_true.mp hq'.2 J hJ
  rw [hJn] at hJ'
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or] at hJ'
  have := List.all_eq_true.mp hJ' cc hcc
  rw [hJn]
  simpa using this

/-- **THE CONTAINERS' GROUP FACTS AT EVERY PIN** (task #279 K.14/K.15,
inverted): the pins are structurally distinct, every pin's container
has a stored `containerInfo?`, and every member of that container's
`all`-group recovers the SAME parameter count and the SAME member
names — the group's one datum, which the model tier instantiates a
group-mate's reads at. -/
theorem nestedContainersOk_group {env : Env} {pins : List NestedPin}
    (h : nestedContainersOk env pins = true) :
    (pins.map (·.pin)).Nodup ∧
    ∀ q ∈ pins, ∃ ci : ContainerInfo, containerInfo? env q.container = some ci ∧
      ∀ M ∈ ci.members, ∃ ci' : ContainerInfo, containerInfo? env M.name = some ci' ∧
        ci'.nP = ci.nP ∧ ci'.members.map (·.name) = ci.members.map (·.name) := by
  simp only [nestedContainersOk, pinsDistinct, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hnd, hall⟩ := h
  refine ⟨hnd, fun q hq => ?_⟩
  have hq' := List.all_eq_true.mp hall q hq
  cases hc : containerInfo? env q.container with
  | none => rw [hc] at hq'; exact absurd hq' (by simp)
  | some ci =>
    rw [hc] at hq'
    simp only [containerFactsOk, Bool.and_eq_true] at hq'
    have hg : containerGroupOk env ci = true := hq'.1.1
    simp only [containerGroupOk] at hg
    refine ⟨ci, rfl, fun M hM => ?_⟩
    have hM' := List.all_eq_true.mp hg M hM
    cases hc' : containerInfo? env M.name with
    | none => rw [hc'] at hM'; exact absurd hM' (by simp)
    | some ci' =>
      rw [hc'] at hM'
      simp only [Bool.and_eq_true, beq_iff_eq] at hM'
      exact ⟨ci', rfl, hM'.1, hM'.2⟩

/-! ## The auxiliary block's own constructors, member by member -/

/-- The selection's global indices do not change what it selects: the
length of `ownCtors`-style filter is the plain list's. -/
private theorem zipIdxSel_filter_length {mm : Nat} :
    ∀ (l : List MutualCtor) (s : Nat),
      (((l.zipIdx s).map fun (c, J) => (J, c)).filter fun (_, c) => c.member == mm).length
        = (l.filter fun c => c.member == mm).length := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons c l ih =>
    intro s
    by_cases hc : c.member = mm
    · simp [List.zipIdx_cons, hc, ih (s + 1)]
    · simp [List.zipIdx_cons, hc, ih (s + 1)]

private theorem ownCtors_length_filter (b : MutualBlock) (mm : Nat) :
    (b.ownCtors mm).length = (b.ctors.filter fun c => c.member == mm).length :=
  zipIdxSel_filter_length b.ctors 0

/-- Below a group's index nothing is selected: `auxBlock` tags every
constructor of the type at index `i` with `i`, so a tag smaller than
every index in the run selects nothing. -/
private theorem auxCtors_filter_nil {lps : List Name} {mm : Nat} :
    ∀ (L : List AuxType) (s : Nat), mm < s →
      (((L.zipIdx s).map fun (t, mIdx) =>
          t.ctors.map fun c =>
            (⟨⟨c.1, lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor)).flatten).filter
        (fun c => c.member == mm) = [] := by
  intro L
  induction L with
  | nil => intro s _; rfl
  | cons a L ih =>
    intro s hs
    simp only [List.zipIdx_cons, List.map_cons, List.flatten_cons, List.filter_append,
      ih (s + 1) (by omega), List.append_nil]
    refine List.filter_eq_nil_iff.mpr (fun c hc => ?_)
    obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
    simp only [beq_iff_eq]
    omega

/-- **The tagged flattening counts one group**: the constructors of the
flattened, index-tagged type list whose tag is `s + d` are exactly the
`d`-th type's. -/
private theorem auxCtors_filter_length {lps : List Name} {mm : Nat} :
    ∀ (L : List AuxType) (s d : Nat) (t : AuxType), L[d]? = some t → mm = s + d →
      ((((L.zipIdx s).map fun (t, mIdx) =>
          t.ctors.map fun c =>
            (⟨⟨c.1, lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor)).flatten).filter
        fun c => c.member == mm).length = t.ctors.length := by
  intro L
  induction L with
  | nil => intro s d t ht _; exact absurd ht (by simp)
  | cons a L ih =>
    intro s d t ht hmm
    simp only [List.zipIdx_cons, List.map_cons, List.flatten_cons, List.filter_append,
      List.length_append]
    cases d with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
      rw [← ht]
      have h1 : ∀ c ∈ (a.ctors.map fun c =>
          (⟨⟨c.1, lps, c.2.1⟩, c.2.2, s⟩ : MutualCtor)), (c.member == mm) = true := by
        intro c hc
        obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
        simp only [beq_iff_eq]
        omega
      rw [List.filter_eq_self.mpr h1, auxCtors_filter_nil L (s + 1) (by omega)]
      simp
    | succ d =>
      simp only [List.getElem?_cons_succ] at ht
      have h0 : ((a.ctors.map fun c =>
          (⟨⟨c.1, lps, c.2.1⟩, c.2.2, s⟩ : MutualCtor)).filter
            fun c => c.member == mm) = [] := by
        refine List.filter_eq_nil_iff.mpr (fun c hc => ?_)
        obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
        simp only [beq_iff_eq]
        omega
      rw [h0, List.length_nil, Nat.zero_add]
      exact ih (s + 1) d t ht (by omega)

/-- **A MEMBER'S OWN CONSTRUCTORS ARE ITS OWN TYPE'S** (task #315 M6
s9): `auxBlock` flattens the elimination's type list into `b.ctors`,
tagging each constructor with its type's index (`auxBlock_fields`), and
`MutualBlock.ownCtors mIdx` selects the constructors carrying that tag
— so member `mIdx`'s own run has exactly the `mIdx`-th type's
constructors. -/
theorem auxBlock_ownCtors_length {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (hb : auxBlock p st = some b) :
    ∀ (mIdx : Nat) (t : AuxType), st.types[mIdx]? = some t →
      (b.ownCtors mIdx).length = t.ctors.length := by
  intro mIdx t ht
  obtain ⟨-, -, -, hct⟩ := auxBlock_fields hb
  rw [ownCtors_length_filter, hct]
  exact auxCtors_filter_length st.types 0 mIdx t ht (by omega)

end ConLeche
