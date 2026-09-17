module

public import ConLeche.Kernel.Inductives.NestedInstall
import ConLeche.Verify.Inductives.NestedInv

public section

/-!
# The nested install's group and pin records, inverted (task #315)

Four Bools and one loop of `ConLeche/Kernel/Inductives/NestedInstall.lean`
read back as the packages the model tier consumes, plus the one fact
about `Expr.stripPis` they all rest on.

* **The mint groups** (`nestedGroupsOk_inv`, K.29).  Per pin: the pin
  lies in its own group, the group is a contiguous block of the pin
  list of the container's `all`-group's size, the group's `i`-th pin
  copies the container's `i`-th member, the group's copies share the
  level instantiation and the pin's components, and the components'
  count is the container's parameter count.
* **The container's block** (`containerInfo?_inv`).  Everything the
  reconstruction establishes: the stored former and recursor of the
  container itself, that the container is one of the members it
  returns, that the members' names are distinct, and per member its
  stored former, its recursor (at the SAME rule prefix and the same
  level parameters), and its constructors — one per recursor rule, in
  rule order, each a stored `ctorInfo` at the group's parameter count.
* **The pins' front door** (`nestedPinsOk_inv`, `pinsClosed_inv`,
  `pinsScoped_inv`).  The loop's two syntactic tests and its inference,
  per pin; and K.30's scope — the first type's openers, every pin's free
  variables among them, no loose bound variable.
* **A telescope ending in a sort has ONE binder count**
  (`stripPis_sort_unique`): `stripPis` is deterministic in the count,
  so two readings of the same former agree on everything.

The index count's telescope (`auxIdxCount_stripPis`) is already
`ConLeche/Verify/Inductives/NestedInv.lean`'s and is not repeated here.
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## (A) Telescopes -/

private theorem stripPis_sort_unique_aux :
    ∀ (n : Nat) {e : Expr} {m : Nat} {bs bs' : List (Expr × BinderMeta)} {s s' : Level},
      e.stripPis n = some (bs, Expr.sort s) → e.stripPis m = some (bs', Expr.sort s') →
      n = m ∧ bs = bs' ∧ s = s'
  | 0, e, m, bs, bs', s, s', h, h' => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases m with
    | zero =>
      simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq, Expr.sort.injEq] at h'
      exact ⟨rfl, h'.1, h'.2⟩
    | succ m => simp only [Expr.stripPis] at h'; exact nomatch h'
  | n + 1, e, m, bs, bs', s, s', h, h' => by
    match e, h, h' with
    | .forallE ty b mb, h, h' =>
      cases m with
      | zero =>
        simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h'
        exact nomatch h'.2
      | succ m =>
        simp only [Expr.stripPis] at h h'
        cases hb : b.stripPis n with
        | none => rw [hb] at h; exact nomatch h
        | some r =>
          obtain ⟨bs₀, body₀⟩ := r
          rw [hb] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hb' : b.stripPis m with
          | none => rw [hb'] at h'; exact nomatch h'
          | some r' =>
            obtain ⟨bs₁, body₁⟩ := r'
            rw [hb'] at h'
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
            obtain ⟨rfl, rfl⟩ := h'
            obtain ⟨rfl, rfl, rfl⟩ := stripPis_sort_unique_aux n hb hb'
            exact ⟨rfl, rfl, rfl⟩

/-- **A TELESCOPE ENDING IN A SORT HAS ONE BINDER COUNT** (task #315):
`stripPis` peels `∀`s greedily, so a former read at two counts is read
at the same one, with the same binders and the same sort. -/
theorem stripPis_sort_unique {e : Expr} {n m : Nat} {bs bs' : List (Expr × BinderMeta)}
    {s s' : Level} (h : e.stripPis n = some (bs, .sort s))
    (h' : e.stripPis m = some (bs', .sort s')) :
    n = m ∧ bs = bs' ∧ s = s' :=
  stripPis_sort_unique_aux n h h'

/-! ## (B) The pins' front door -/

/-- **THE PINS' SCOPE** (task #315): `pinsClosed` is the Bool the run
relation records; this is the pair of facts it stands for, per pin. -/
theorem pinsClosed_inv {nP : Nat} {pins : List NestedPin}
    (h : pinsClosed nP pins = true) :
    ∀ q ∈ pins, (Expr.abstractRange q.pin 0 nP 0).hasFvar = false ∧
      (Expr.abstractRange q.pin 0 nP 0).looseBVarsBounded nP = true := by
  unfold pinsClosed at h
  intro q hq
  have hq' := List.all_eq_true.mp h q hq
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hq'
  exact hq'

/-- **THE PINS' SCOPE, INVERTED** (task #315 K.30, consumed at U-20):
`pinsScoped` is the Bool the run relation records; this is what it
stands for.  The FIRST type's parameter openers exist, and every pin
has no loose bound variable and every free variable — annotation
included — is one of those openers, at its own index. -/
theorem pinsScoped_inv {nP : Nat} {st : ElimState} (h : pinsScoped nP st = true) :
    ∃ (t₀ : AuxType) (params : List Expr) (o : Expr),
      st.types.head? = some t₀ ∧ openPisAtFvars nP t₀.type 0 = some (params, o) ∧
      ∀ q ∈ st.pins, q.pin.looseBVarsBounded 0 = true ∧
        ∀ l ∈ q.pin.fvarLeaves, Expr.fvar l.1 l.2 ∈ params := by
  unfold pinsScoped at h
  cases ht : st.types.head? with
  | none => rw [ht] at h; exact nomatch h
  | some t₀ =>
    rw [ht, Option.bind_some] at h
    cases ho : openPisAtFvars nP t₀.type 0 with
    | none => rw [ho] at h; exact nomatch h
    | some po =>
      rw [ho] at h
      obtain ⟨params, o⟩ := po
      refine ⟨t₀, params, o, rfl, ho, ?_⟩
      intro q hq
      have hq' := List.all_eq_true.mp h q hq
      simp only [Bool.and_eq_true] at hq'
      refine ⟨hq'.1, fun l hl => ?_⟩
      have hl' := List.all_eq_true.mp hq'.2 l hl
      exact List.mem_of_getElem? (beq_iff_eq.mp hl')

/-- **POST-CHECK (a), INVERTED** (task #315): the loop's two syntactic
tests and its inference, at every pin. -/
theorem nestedPinsOk_inv {F : Nat} {env : Env} {nP : Nat} :
    ∀ {pins : List NestedPin},
      nestedPinsOk (m := CheckM) (fueledOps mode F) env nP pins = .ok () →
      ∀ q ∈ pins,
        (Expr.abstractRange q.pin 0 nP 0).hasFvar = false ∧
        (Expr.abstractRange q.pin 0 nP 0).looseBVarsBounded nP = true ∧
        ∃ ty : Expr, inferTypeCore mode env F nP q.pin = .ok ty := by
  intro pins
  induction pins with
  | nil => intro _ q hq; exact absurd hq (by simp)
  | cons q₀ rest ih =>
    intro h q hq
    simp only [nestedPinsOk] at h
    by_cases hb : (!(Expr.abstractRange q₀.pin 0 nP 0).hasFvar &&
        (Expr.abstractRange q₀.pin 0 nP 0).looseBVarsBounded nP) = true
    · rw [if_pos hb] at h
      obtain ⟨ty, hty, hrest⟩ := exceptBind_ok h
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
      rcases List.mem_cons.mp hq with rfl | hmem
      · exact ⟨hb.1, hb.2, ty, hty⟩
      · exact ih hrest q hmem
    · rw [if_neg hb] at h
      simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-! ## (C) The mint groups -/

/-- **K.29's RECORD, INVERTED** (task #315): `nestedGroupsOk` is a Bool
over the pin range; this is the package it stands for.  At every pin
`q` the container is recovered at this environment, the copy at
`p.k + q` carries the source K.28 certified, and the pin's GROUP is a
contiguous block of the pin list: `q` lies in it, it ends inside the
list, it is as long as the container's `all`-group, the components are
as many as the container's parameters, and its `i`-th pin copies the
container's `i`-th member — same group fields, same level
instantiation, same components. -/
theorem nestedGroupsOk_inv {env : Env} {p : NestedParts} {st : ElimState}
    (h : nestedGroupsOk env p st = true) :
    ∀ (q : Nat) (qn : NestedPin), st.pins[q]? = some qn →
      ∃ (t : AuxType) (ci : ContainerInfo) (Jn : Name) (lvls : List Level) (Ds : List Expr),
        st.types[p.k + q]? = some t ∧ containerInfo? env qn.container = some ci ∧
        t.src = some (Jn, lvls, Ds) ∧
        qn.grpBase ≤ q ∧ q < qn.grpBase + qn.grpSize ∧
        qn.grpBase + qn.grpSize ≤ st.pins.length ∧
        qn.grpSize = ci.members.length ∧ Ds.length = ci.nP ∧
        ∀ i, i < qn.grpSize →
          ∃ (qi : NestedPin) (Ji : ContainerMember) (ti : AuxType),
            st.pins[qn.grpBase + i]? = some qi ∧ ci.members[i]? = some Ji ∧
            st.types[p.k + qn.grpBase + i]? = some ti ∧
            qi.container = Ji.name ∧ qi.grpBase = qn.grpBase ∧ qi.grpSize = qn.grpSize ∧
            ti.src = some (Ji.name, lvls, Ds) := by
  unfold nestedGroupsOk at h
  intro q qn hqn
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hqn
  have hq := List.all_eq_true.mp h q (List.mem_range.mpr hlt)
  rw [hqn] at hq
  cases ht : st.types[p.k + q]? with
  | none => simp only [ht] at hq; exact absurd hq (by simp)
  | some t =>
    simp only [ht] at hq
    cases hci : containerInfo? env qn.container with
    | none => simp only [hci] at hq; exact absurd hq (by simp)
    | some ci =>
      cases hsrc : t.src with
      | none => simp only [hci, hsrc] at hq; exact absurd hq (by simp)
      | some tr =>
        obtain ⟨Jn, lvls, Ds⟩ := tr
        simp only [hci, hsrc, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hq
        obtain ⟨⟨⟨⟨⟨hb1, hb2⟩, hb3⟩, hsz⟩, hDs⟩, hall⟩ := hq
        refine ⟨t, ci, Jn, lvls, Ds, rfl, rfl, hsrc, hb1, hb2, hb3, hsz, hDs, ?_⟩
        intro i hi
        have hqi := List.all_eq_true.mp hall i (List.mem_range.mpr hi)
        cases hpi : st.pins[qn.grpBase + i]? with
        | none => simp only [hpi] at hqi; exact absurd hqi (by simp)
        | some qi =>
          cases hJi : ci.members[i]? with
          | none => simp only [hpi, hJi] at hqi; exact absurd hqi (by simp)
          | some Ji =>
            cases hti : st.types[p.k + qn.grpBase + i]? with
            | none => simp only [hpi, hJi, hti] at hqi; exact absurd hqi (by simp)
            | some ti =>
              cases htsrc : ti.src with
              | none =>
                simp only [hpi, hJi, hti, htsrc, Bool.and_false] at hqi
                exact absurd hqi (by simp)
              | some tr =>
                obtain ⟨Jn', lvls', Ds'⟩ := tr
                simp only [hpi, hJi, hti, htsrc, Bool.and_eq_true, beq_iff_eq] at hqi
                obtain ⟨⟨⟨hc, hgb⟩, hgs⟩, ⟨hJ', hl'⟩, hD'⟩ := hqi
                subst hJ'; subst hl'; subst hD'
                exact ⟨qi, Ji, ti, rfl, rfl, rfl, hc, hgb, hgs, htsrc⟩

/-! ## (D) The container's block -/

/-- A successful `mapM` in `Option` preserves the length (the twin of
`NestedElimInv.lean`'s `mapM_option_length`, which this module does not
import). -/
private theorem mapM_option_len {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    simp [← h]
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨b, -, bs, hbs, rfl⟩ := h
    simp [mapM_option_len hbs]

/-- **THE CONTAINER'S BLOCK, INVERTED** (task #315): everything
`containerInfo?` establishes about the group it returns. -/
theorem containerInfo?_inv {env : Env} {I : Name} {ci : ContainerInfo}
    (h : containerInfo? env I = some ci) :
    ∃ (cvT : ConstantVal) (caps : IndCaps) (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env.find? I = some (.indInfo cvT caps) ∧
      env.find? (I.str "rec") = some (.recInfo cvR mI rP rules) ∧
      I ∈ ci.members.map (·.name) ∧ (ci.members.map (·.name)).Nodup ∧
      ∀ M ∈ ci.members,
        ∃ (cvC : ConstantVal) (capsC : IndCaps) (cvRc : ConstantVal) (mIc : Nat)
          (rulesC : List RecRule),
          env.find? M.name = some (.indInfo cvC capsC) ∧
          env.find? (M.name.str "rec") = some (.recInfo cvRc mIc rP rulesC) ∧
          M.lps = cvC.levelParams ∧ M.type = cvC.type ∧ cvC.levelParams = cvT.levelParams ∧
          M.ctors.length = rulesC.length ∧
          ∀ (j : Nat) (cc : ContainerCtor), M.ctors[j]? = some cc →
            ∃ (r : RecRule) (cvc : ConstantVal), rulesC[j]? = some r ∧ cc.name = r.ctor ∧
              env.find? r.ctor = some (.ctorInfo cvc ci.nP cc.nFields) ∧ cc.type = cvc.type := by
  unfold containerInfo? at h
  by_cases hq : (I == quotName) = true
  · rw [if_pos hq] at h; exact nomatch h
  · rw [if_neg hq] at h
    cases hfI : env.find? I with
    | none => simp only [hfI] at h; exact nomatch h
    | some cI =>
      cases cI with
      | indInfo cvT caps =>
        cases hfR : env.find? (I.str "rec") with
        | none => simp only [hfI, hfR] at h; exact nomatch h
        | some cR =>
          cases cR with
          | recInfo cvR mI rP rules =>
            simp only [hfI, hfR, bind, Option.bind] at h
            by_cases hle : rP ≤ mI
            case neg => rw [if_neg hle] at h; exact nomatch h
            rw [if_pos hle] at h
            split at h
            case h_1 => exact nomatch h
            rename_i nP hnP
            dsimp only at h
            split at h
            case h_1 => exact nomatch h
            rename_i xx hxx
            dsimp only at h
            split at h
            case isFalse => exact nomatch h
            rename_i hnames
            split at h
            case h_1 => exact nomatch h
            rename_i members hmembers
            dsimp only at h
            obtain rfl := Option.some.inj h
            dsimp only
            clear h hnP hxx hle hq
            -- the members' loop, inverted at one position
            have hstep : ∀ (i : Nat) (C : Name) (M : ContainerMember),
                (containerMembersGo env nP (rP + 1) 0 xx.snd)[i]? = some C →
                members[i]? = some M →
                M.name = C ∧
                ∃ (cvC : ConstantVal) (capsC : IndCaps) (cvRc : ConstantVal) (mIc : Nat)
                  (rulesC : List RecRule),
                  env.find? M.name = some (.indInfo cvC capsC) ∧
                  env.find? (M.name.str "rec") = some (.recInfo cvRc mIc rP rulesC) ∧
                  M.lps = cvC.levelParams ∧ M.type = cvC.type ∧
                  cvC.levelParams = cvT.levelParams ∧ M.ctors.length = rulesC.length ∧
                  ∀ (j : Nat) (cc : ContainerCtor), M.ctors[j]? = some cc →
                    ∃ (r : RecRule) (cvc : ConstantVal), rulesC[j]? = some r ∧ cc.name = r.ctor ∧
                      env.find? r.ctor = some (.ctorInfo cvc nP cc.nFields) ∧ cc.type = cvc.type := by
              intro i C M hC hM
              obtain ⟨M', hM', hf⟩ := mapM_option_inv hmembers i C hC
              obtain rfl : M' = M := Option.some.inj (hM'.symm.trans hM)
              split at hf
              case h_1 => exact nomatch hf
              rename_i cC hfC
              dsimp only at hf
              split at hf
              case h_2 => exact nomatch hf
              rename_i cvC capsC
              split at hf
              case h_1 => exact nomatch hf
              rename_i cRc hfRc
              dsimp only at hf
              split at hf
              case h_2 => exact nomatch hf
              rename_i cvRc mIc rPc rulesC
              split at hf
              case isFalse => exact nomatch hf
              rename_i hcond
              split at hf
              case h_1 => exact nomatch hf
              rename_i ctors hctors
              dsimp only at hf
              obtain rfl := Option.some.inj hf
              simp only [Bool.and_eq_true, beq_iff_eq] at hcond
              obtain ⟨rfl, hlps⟩ := hcond
              refine ⟨rfl, cvC, capsC, cvRc, mIc, rulesC, hfC, hfRc, rfl, rfl, hlps,
                mapM_option_len hctors, ?_⟩
              intro j cc hcc
              obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hcc
              have hjr : j < rulesC.length := by
                rw [← mapM_option_len hctors]; exact hjlt
              obtain ⟨r, hr⟩ : ∃ r, rulesC[j]? = some r :=
                ⟨_, List.getElem?_eq_getElem hjr⟩
              obtain ⟨cc', hcc', hg⟩ := mapM_option_inv hctors j r hr
              obtain rfl : cc' = cc := Option.some.inj (hcc'.symm.trans hcc)
              split at hg
              case h_2 => exact nomatch hg
              rename_i cvc nPc nF hfc
              split at hg
              case isFalse => exact nomatch hg
              rename_i hnP'
              simp only [beq_iff_eq] at hnP'
              subst hnP'
              obtain rfl := Option.some.inj hg
              exact ⟨r, cvc, hr, rfl, hfc, rfl⟩
            -- the three readings
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hnames
            have hlen : members.length = (containerMembersGo env nP (rP + 1) 0 xx.snd).length :=
              mapM_option_len hmembers
            have hmapnames : members.map (·.name) =
                containerMembersGo env nP (rP + 1) 0 xx.snd := by
              refine List.ext_getElem? (fun i => ?_)
              rw [List.getElem?_map]
              cases hM : members[i]? with
              | none =>
                have hile : members.length ≤ i := List.getElem?_eq_none_iff.mp hM
                simp only [Option.map_none]
                exact (List.getElem?_eq_none (by omega)).symm
              | some M =>
                obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hM
                obtain ⟨C, hC⟩ : ∃ C, (containerMembersGo env nP (rP + 1) 0 xx.snd)[i]? = some C :=
                  ⟨_, List.getElem?_eq_getElem (by omega)⟩
                rw [hC, Option.map_some, (hstep i C M hC hM).1]
            refine ⟨cvT, caps, cvR, mI, rP, rules, rfl, rfl, ?_, ?_, ?_⟩
            · have hI : I ∈ containerMembersGo env nP (rP + 1) 0 xx.snd :=
                List.mem_of_elem_eq_true hnames.1
              rw [hmapnames]; exact hI
            · rw [hmapnames]; exact hnames.2
            · intro M hM
              obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hM
              obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hi
              obtain ⟨C, hC⟩ : ∃ C, (containerMembersGo env nP (rP + 1) 0 xx.snd)[i]? = some C :=
                ⟨_, List.getElem?_eq_getElem (by omega)⟩
              exact (hstep i C M hC hi).2
          | _ => simp only [hfI, hfR] at h; exact nomatch h
      | _ => simp only [hfI] at h; exact nomatch h


/-! ## A group's members are determined by their names (task #315 L-B)

A pin records its OWN container's group (`containerInfo?` at the pin's
container), while the group's block model is the BASE pin's
(`baseInfo`).  K.29 ties the two only by the members' NAMES and the
parameter count; the copies' identities read the member RECORD (its
type and its constructors' types and field counts), so the two records
must be the same.  They are: every field of a `ContainerMember` is a
function of the environment at the member's name, with the group's
`nP` the only other input — the type and level parameters off the
member's own `indInfo`, the constructors off its own recursor's rules
and their `ctorInfo`s. -/

/-- **A container group's member record is determined by its name** at
groups with the same parameter count. -/
theorem containerInfo?_member_det {env : Env} {I₁ I₂ : Name} {ci₁ ci₂ : ContainerInfo}
    (h₁ : containerInfo? env I₁ = some ci₁) (h₂ : containerInfo? env I₂ = some ci₂)
    (hnP : ci₁.nP = ci₂.nP) {M₁ M₂ : ContainerMember}
    (hm₁ : M₁ ∈ ci₁.members) (hm₂ : M₂ ∈ ci₂.members) (hname : M₁.name = M₂.name) :
    M₁ = M₂ := by
  obtain ⟨cvT₁, caps₁, cvR₁, mI₁, rP₁, rules₁, -, -, -, -, hall₁⟩ := containerInfo?_inv h₁
  obtain ⟨cvT₂, caps₂, cvR₂, mI₂, rP₂, rules₂, -, -, -, -, hall₂⟩ := containerInfo?_inv h₂
  obtain ⟨cvC₁, capsC₁, cvRc₁, mIc₁, rulesC₁, hf₁, hr₁, hlps₁, hty₁, -, hlen₁, hct₁⟩ := hall₁ M₁ hm₁
  obtain ⟨cvC₂, capsC₂, cvRc₂, mIc₂, rulesC₂, hf₂, hr₂, hlps₂, hty₂, -, hlen₂, hct₂⟩ := hall₂ M₂ hm₂
  rw [hname] at hf₁ hr₁
  obtain rfl : cvC₁ = cvC₂ := (ConstantInfo.indInfo.inj (Option.some.inj (hf₁.symm.trans hf₂))).1
  obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj (hr₁.symm.trans hr₂))
  have hctors : M₁.ctors = M₂.ctors := by
    refine List.ext_getElem? fun j => ?_
    cases hc₁ : M₁.ctors[j]? with
    | none =>
      have : M₂.ctors[j]? = none := by
        rw [List.getElem?_eq_none_iff] at hc₁ ⊢; omega
      rw [this]
    | some cc₁ =>
      have hjlt : j < M₂.ctors.length := by
        have := (List.getElem?_eq_some_iff.mp hc₁).1
        omega
      obtain ⟨cc₂, hc₂⟩ : ∃ cc₂, M₂.ctors[j]? = some cc₂ := ⟨_, List.getElem?_eq_getElem hjlt⟩
      obtain ⟨r₁, cvc₁, hr₁', hn₁, hfc₁, htc₁⟩ := hct₁ j cc₁ hc₁
      obtain ⟨r₂, cvc₂, hr₂', hn₂, hfc₂, htc₂⟩ := hct₂ j cc₂ hc₂
      obtain rfl : r₁ = r₂ := Option.some.inj (hr₁'.symm.trans hr₂')
      rw [hnP] at hfc₁
      obtain ⟨rfl, -, hnf⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfc₁.symm.trans hfc₂))
      have hcc : cc₁ = cc₂ := by
        obtain ⟨n₁, t₁, f₁⟩ := cc₁
        obtain ⟨n₂, t₂, f₂⟩ := cc₂
        simp only at hn₁ hn₂ htc₁ htc₂ hnf ⊢
        rw [hn₁, hn₂, htc₁, htc₂, hnf]
      rw [hc₂, hcc]
  obtain ⟨n₁, l₁, t₁, cs₁⟩ := M₁
  obtain ⟨n₂, l₂, t₂, cs₂⟩ := M₂
  simp only at hname hlps₁ hlps₂ hty₁ hty₂ hctors ⊢
  rw [hname, hlps₁, hlps₂, hty₁, hty₂, hctors]

/-- **Two groups agreeing on their parameter count and member NAMES are
one group** — every member record is a function of the environment at
its name and the parameter count (`containerInfo?_member_det`). -/
theorem containerInfo?_eq_of_names {env : Env} {I₁ I₂ : Name} {ci₁ ci₂ : ContainerInfo}
    (h₁ : containerInfo? env I₁ = some ci₁) (h₂ : containerInfo? env I₂ = some ci₂)
    (hnP : ci₁.nP = ci₂.nP) (hnames : ci₁.members.map (·.name) = ci₂.members.map (·.name)) :
    ci₁ = ci₂ := by
  have hmem : ci₁.members = ci₂.members := by
    apply List.ext_getElem?
    intro n
    have := congrArg (fun l => l[n]?) hnames
    simp only [List.getElem?_map] at this
    cases h1 : ci₁.members[n]? with
    | none =>
      rw [h1] at this
      cases h2 : ci₂.members[n]? with
      | none => rfl
      | some M₂ => rw [h2] at this; exact nomatch this
    | some M₁ =>
      rw [h1] at this
      cases h2 : ci₂.members[n]? with
      | none => rw [h2] at this; exact nomatch this
      | some M₂ =>
        rw [h2] at this
        exact congrArg some (containerInfo?_member_det h₁ h₂ hnP (List.mem_of_getElem? h1)
          (List.mem_of_getElem? h2) (Option.some.inj this))
  cases ci₁; cases ci₂
  simp only [ContainerInfo.mk.injEq] at hnP hmem ⊢
  exact ⟨hnP, hmem⟩

/-- **A member's record is determined by its name alone AT A
CONSTRUCTOR POSITION** (task #315 L-B): two groups that both list a
member of the same name agree on its level parameters, its type, and —
at every position where both list a constructor — on the constructor
record.  Unlike `containerInfo?_member_det` this needs NO hypothesis
about the groups' parameter counts: the two `ctorInfo`s the position
names are the same stored constant, which pins the counts too.  It is
what lets the elimination's own group (the container `I` whose
occurrence was rewritten, `elimNested_copyCtors`) and the PIN's group
(the copied member's own, K.28) be used interchangeably. -/
theorem containerInfo?_member_ctor_det {env : Env} {I₁ I₂ : Name} {ci₁ ci₂ : ContainerInfo}
    (h₁ : containerInfo? env I₁ = some ci₁) (h₂ : containerInfo? env I₂ = some ci₂)
    {M₁ M₂ : ContainerMember} (hm₁ : M₁ ∈ ci₁.members) (hm₂ : M₂ ∈ ci₂.members)
    (hname : M₁.name = M₂.name) {j : Nat} {cc₁ cc₂ : ContainerCtor}
    (hc₁ : M₁.ctors[j]? = some cc₁) (hc₂ : M₂.ctors[j]? = some cc₂) :
    M₁.lps = M₂.lps ∧ M₁.type = M₂.type ∧ ci₁.nP = ci₂.nP ∧ cc₁ = cc₂ := by
  obtain ⟨cvT₁, caps₁, cvR₁, mI₁, rP₁, rules₁, -, -, -, -, hall₁⟩ := containerInfo?_inv h₁
  obtain ⟨cvT₂, caps₂, cvR₂, mI₂, rP₂, rules₂, -, -, -, -, hall₂⟩ := containerInfo?_inv h₂
  obtain ⟨cvC₁, capsC₁, cvRc₁, mIc₁, rulesC₁, hf₁, hr₁, hlps₁, hty₁, -, hlen₁, hct₁⟩ := hall₁ M₁ hm₁
  obtain ⟨cvC₂, capsC₂, cvRc₂, mIc₂, rulesC₂, hf₂, hr₂, hlps₂, hty₂, -, hlen₂, hct₂⟩ := hall₂ M₂ hm₂
  rw [hname] at hf₁ hr₁
  obtain rfl : cvC₁ = cvC₂ := (ConstantInfo.indInfo.inj (Option.some.inj (hf₁.symm.trans hf₂))).1
  obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj (hr₁.symm.trans hr₂))
  obtain ⟨r₁, cvc₁, hr₁', hn₁, hfc₁, htc₁⟩ := hct₁ j cc₁ hc₁
  obtain ⟨r₂, cvc₂, hr₂', hn₂, hfc₂, htc₂⟩ := hct₂ j cc₂ hc₂
  obtain rfl : r₁ = r₂ := Option.some.inj (hr₁'.symm.trans hr₂')
  obtain ⟨rfl, hnP, hnf⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfc₁.symm.trans hfc₂))
  refine ⟨by rw [hlps₁, hlps₂], by rw [hty₁, hty₂], hnP, ?_⟩
  obtain ⟨n₁, t₁, f₁⟩ := cc₁
  obtain ⟨n₂, t₂, f₂⟩ := cc₂
  simp only at hn₁ hn₂ htc₁ htc₂ hnf ⊢
  rw [hn₁, hn₂, htc₁, htc₂, hnf]

/-! ## (E) The uniformity walk (task #315)

`uniformIndOccsOk` is `check_uniform_ind_occs`, the syntactic walk
K.14's `containerFactsOk` records at every pinned container: every
occurrence of a member of the container's group, anywhere in a stored
constructor type, is that member applied to the group's own parameter
variables and its own universe levels.  The model tier consumes it at
ONE place — a constructor field whose head is a group member — and
needs it there as a statement about the field's OWN binder depth, so
the three steps below take the walk from the constructor type down to
the field and read the spine off it. -/

/-- **The walk's prune, as an introduction rule** (task #315): a
subterm mentioning no member of the block carries no occurrence to
check, so the walk answers `true` at every offset. -/
private theorem uniformIndOccsE_of_no_mention {names : List Name} {lvls : List Level}
    {nP o : Nat} {e : Expr} (h : names.any (fun T => e.mentionsConst T) = false) :
    uniformIndOccsE names lvls nP o e = true := by
  rw [uniformIndOccsE.eq_def]
  simp [h]

/-- The walk at a node the prune does not dismiss and whose
`uniformOccNode` rejects: the walk rejects too. -/
private theorem uniformIndOccsE_of_node_none {names : List Name} {lvls : List Level}
    {nP o : Nat} {e : Expr} (hm : names.any (fun T => e.mentionsConst T) = true)
    (hn : uniformOccNode names lvls nP o e = none) :
    uniformIndOccsE names lvls nP o e = false := by
  rw [uniformIndOccsE.eq_def]
  simp [hm, hn]

/-- The walk at an application the prune does not dismiss and whose
`uniformOccNode` says "descend": both halves are walked at the SAME
offset. -/
private theorem uniformIndOccsE_app_inv {names : List Name} {lvls : List Level}
    {nP o : Nat} {f a : Expr}
    (hm : names.any (fun T => (Expr.app f a).mentionsConst T) = true)
    (hn : uniformOccNode names lvls nP o (Expr.app f a) = some false)
    (h : uniformIndOccsE names lvls nP o (Expr.app f a) = true) :
    uniformIndOccsE names lvls nP o f = true ∧ uniformIndOccsE names lvls nP o a = true := by
  have hb : uniformIndOccsE names lvls nP o (Expr.app f a) =
      (uniformIndOccsE names lvls nP o f && uniformIndOccsE names lvls nP o a) := by
    rw [uniformIndOccsE.eq_def]
    simp [hm, hn]
  rw [hb] at h
  simpa using h

/-- **The Π node of the walk, inverted** (task #315): the walk of a `∀`
is the walk of its domain at the same offset and of its body one binder
deeper — in the pruned case both by the prune on the two parts. -/
private theorem uniformIndOccsE_forallE_inv {names : List Name} {lvls : List Level}
    {nP o : Nat} {ty b : Expr} {bm : BinderMeta}
    (h : uniformIndOccsE names lvls nP o (.forallE ty b bm) = true) :
    uniformIndOccsE names lvls nP o ty = true ∧
      uniformIndOccsE names lvls nP (o + 1) b = true := by
  cases hm : names.any (fun T => (Expr.forallE ty b bm).mentionsConst T) with
  | false =>
    have hsplit : ∀ T ∈ names, Expr.mentionsConst T ty = false ∧ Expr.mentionsConst T b = false := by
      intro T hT
      have hT' : (Expr.mentionsConst T ty || Expr.mentionsConst T b) = false := by
        have h0 := List.any_eq_false.mp hm T hT
        simpa [Expr.mentionsConst] using h0
      exact Bool.or_eq_false_iff.mp hT'
    exact ⟨uniformIndOccsE_of_no_mention
        (List.any_eq_false.mpr fun T hT => by simp [(hsplit T hT).1]),
      uniformIndOccsE_of_no_mention
        (List.any_eq_false.mpr fun T hT => by simp [(hsplit T hT).2])⟩
  | true =>
    have hb : uniformIndOccsE names lvls nP o (.forallE ty b bm) =
        (uniformIndOccsE names lvls nP o ty && uniformIndOccsE names lvls nP (o + 1) b) := by
      have hn : uniformOccNode names lvls nP o (Expr.forallE ty b bm) = some false := rfl
      rw [uniformIndOccsE.eq_def]
      simp [hm, hn]
    rw [hb] at h
    simpa using h

/-- **THE WALK AT ONE BINDER OF A TELESCOPE** (task #315): the walk of
a `∀`-telescope visits the `i`-th binder's domain at the offset the
telescope's start had, raised by `i` — the binder depth that domain
actually sits at.  The prune is no obstacle: a type mentioning no
member has no part that mentions one. -/
theorem uniformIndOccsE_stripPis {names : List Name} {lvls : List Level} {nP : Nat} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {res : Expr} {o i : Nat}
      {bd : Expr × BinderMeta},
      e.stripPis n = some (bs, res) → bs[i]? = some bd →
      uniformIndOccsE names lvls nP o e = true →
      uniformIndOccsE names lvls nP (o + i) bd.1 = true
  | 0, e, bs, res, o, i, bd, h, hi, _ => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact absurd hi (by simp)
  | n + 1, e, bs, res, o, i, bd, h, hi, hw => by
    match e, h, hw with
    | .forallE ty b m, h, hw =>
      simp only [Expr.stripPis] at h
      cases hb : b.stripPis n with
      | none => rw [hb] at h; exact nomatch h
      | some r =>
        obtain ⟨bs₀, body₀⟩ := r
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hty, hbody⟩ := uniformIndOccsE_forallE_inv hw
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          simpa using hty
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi
          have := uniformIndOccsE_stripPis n hb hi hbody
          rw [show o + (i + 1) = o + 1 + i by omega]
          exact this

/-- `uniformOccNode` at a constant-headed spine, with the head one of
the block's names: the node's three answers, spelled out. -/
private theorem uniformOccNode_spine {names : List Name} {lvls : List Level} {nP o : Nat}
    {T : Name} {us : List Level} {args : List Expr} (hT : names.contains T = true) :
    uniformOccNode names lvls nP o (Expr.mkAppN (.const T us) args) =
      (if args.length > nP then some false
       else if args.length == nP && decide (o ≥ nP) && us == lvls &&
           (List.range nP).all (fun i => args[i]? == some (Expr.bvar (o - 1 - i))) then
         some true
       else none) := by
  have hfn : (Expr.mkAppN (Expr.const T us) args).getAppFn = .const T us := by
    rw [Expr.getAppFn_mkAppN]; rfl
  have hargs : (Expr.mkAppN (Expr.const T us) args).getAppArgs = args := by
    rw [Expr.getAppArgs_mkAppN]; rfl
  simp only [uniformOccNode, hfn, hargs, hT, if_true]

/-- A constant-headed spine mentions its head. -/
private theorem mentionsConst_spine_any {names : List Name} {T : Name} {us : List Level}
    {args : List Expr} (hT : names.contains T = true) :
    names.any (fun T' => (Expr.mkAppN (Expr.const T us) args).mentionsConst T') = true :=
  List.any_eq_true.mpr ⟨T, List.mem_of_elem_eq_true hT,
    Expr.mentionsConst_mkAppN_head args (.const T us) (by simp [Expr.mentionsConst])⟩

private theorem uniformIndOccsE_spine_aux {names : List Name} {lvls : List Level} {nP : Nat}
    {T : Name} {us : List Level} (hT : names.contains T = true) :
    ∀ (k : Nat) {args : List Expr} {o : Nat}, args.length = nP + k →
      uniformIndOccsE names lvls nP o (Expr.mkAppN (.const T us) args) = true →
      us = lvls ∧ nP ≤ o ∧
        args.take nP = (List.range nP).map (fun i => Expr.bvar (o - 1 - i)) := by
  intro k
  induction k with
  | zero =>
    intro args o hlen h
    by_cases hc : (args.length == nP && decide (o ≥ nP) && us == lvls &&
        (List.range nP).all (fun i => args[i]? == some (Expr.bvar (o - 1 - i)))) = true
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨-, ho⟩, hus⟩, hall⟩ := hc
      refine ⟨hus, ho, ?_⟩
      rw [List.take_of_length_le (by omega)]
      refine List.ext_getElem? fun i => ?_
      by_cases hi : i < nP
      · rw [beq_iff_eq.mp (List.all_eq_true.mp hall i (List.mem_range.mpr hi)),
          List.getElem?_map, List.getElem?_range hi]
        rfl
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    · exfalso
      have hn : uniformOccNode names lvls nP o (Expr.mkAppN (.const T us) args) = none := by
        rw [uniformOccNode_spine hT, if_neg (by omega), if_neg hc]
      rw [uniformIndOccsE_of_node_none (mentionsConst_spine_any hT) hn] at h
      exact absurd h (by simp)
  | succ k ih =>
    intro args o hlen h
    obtain ⟨args', a, rfl⟩ : ∃ args' a, args = args' ++ [a] := by
      rcases List.eq_nil_or_concat args with rfl | ⟨L, b, hLb⟩
      · simp only [List.length_nil] at hlen; omega
      · exact ⟨L, b, by simpa using hLb⟩
    have hlen' : args'.length = nP + k := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
    rw [Expr.mkAppN_append_one] at h
    have hn : uniformOccNode names lvls nP o
        (Expr.app (Expr.mkAppN (.const T us) args') a) = some false := by
      rw [← Expr.mkAppN_append_one, uniformOccNode_spine hT,
        if_pos (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
    have hm : names.any (fun T' =>
        (Expr.app (Expr.mkAppN (.const T us) args') a).mentionsConst T') = true := by
      rw [← Expr.mkAppN_append_one]; exact mentionsConst_spine_any hT
    obtain ⟨hf, -⟩ := uniformIndOccsE_app_inv hm hn h
    obtain ⟨h1, h2, h3⟩ := ih hlen' hf
    refine ⟨h1, h2, ?_⟩
    rw [List.take_append_of_le_length (by omega)]
    exact h3

/-- **A MEMBER-HEADED SPINE IS AT THE PARAMETERS** (task #315): if the
walk accepts an expression whose head is one of the block's names and
which carries at least the block's parameters, then the occurrence is
uniform — the head's universe levels are the block's, the offset is
past the parameters, and the first `nP` arguments are exactly the
parameter variables as seen from that offset. -/
theorem uniformIndOccsE_spine {names : List Name} {lvls : List Level} {nP o : Nat}
    {T : Name} {us : List Level} {args : List Expr}
    (hT : names.contains T = true) (hlen : nP ≤ args.length)
    (h : uniformIndOccsE names lvls nP o (Expr.mkAppN (.const T us) args) = true) :
    us = lvls ∧ nP ≤ o ∧ args.take nP = (List.range nP).map (fun i => Expr.bvar (o - 1 - i)) :=
  uniformIndOccsE_spine_aux hT (args.length - nP) (by omega) h

/-- **K.14's UNIFORMITY CLAUSE, READ BACK** (task #315): at every
pinned container and every member of its group, the member's declared
level parameters are distinct and the walk accepts every one of its
stored constructor types at offset `0`. -/
theorem nestedContainersOk_uniform {env : Env} {pins : List NestedPin}
    (h : nestedContainersOk env pins = true)
    {q : NestedPin} (hq : q ∈ pins) {ci : ContainerInfo}
    (hci : containerInfo? env q.container = some ci)
    {M : ContainerMember} (hM : M ∈ ci.members) :
    Name.nodup M.lps = true ∧
    ∀ cty ∈ M.ctors.map (·.type),
      uniformIndOccsE (ci.members.map (·.name)) (M.lps.map Level.param) ci.nP 0 cty = true := by
  simp only [nestedContainersOk, Bool.and_eq_true] at h
  have hq' := List.all_eq_true.mp h.2 q hq
  rw [hci] at hq'
  simp only [containerFactsOk, Bool.and_eq_true] at hq'
  have hM' := List.all_eq_true.mp hq'.2 M hM
  simp only [Bool.and_eq_true] at hM'
  obtain ⟨⟨⟨hnd, hun⟩, -⟩, -⟩ := hM'
  refine ⟨hnd, fun cty hcty => ?_⟩
  simpa only [uniformIndOccsOk] using List.all_eq_true.mp hun cty hcty

/-- **A CONTAINER'S STORED CONSTRUCTOR FIELD HEADED BY A MEMBER SITS AT
THE PARAMETER SPINE** (task #315): the consumer of K.14's uniformity.
The `l`-th field of the `j`-th constructor of a pinned container's
member `M`, read off the stored type's telescope, is a spine whose head
is a group member applied — at its own binder depth `ci.nP + l` — to
the group's universe levels and to the parameter variables
`structPsAt l ci.nP`.  This is what lets the model tier read a nested
field as the container at the block's own parameters. -/
theorem nestedContainersOk_memberSpine {env : Env} {pins : List NestedPin}
    (h : nestedContainersOk env pins = true)
    {q : NestedPin} (hq : q ∈ pins) {ci : ContainerInfo}
    (hci : containerInfo? env q.container = some ci)
    {M : ContainerMember} (hM : M ∈ ci.members)
    {j : Nat} {cc : ContainerCtor} (hcc : M.ctors[j]? = some cc)
    {bs : List (Expr × BinderMeta)} {res : Expr}
    (hstrip : cc.type.stripPis (ci.nP + cc.nFields) = some (bs, res))
    {l : Nat} {bd : Expr × BinderMeta} (hbd : bs[ci.nP + l]? = some bd)
    {T : Name} {us : List Level}
    (hhead : bd.1.getAppFn = Expr.const T us)
    (hT : T ∈ ci.members.map (·.name))
    (hlen : ci.nP ≤ bd.1.getAppArgs.length) :
    us = M.lps.map Level.param ∧
      bd.1.getAppArgs.take ci.nP = ConLeche.structPsAt l ci.nP := by
  obtain ⟨-, hun⟩ := nestedContainersOk_uniform h hq hci hM
  have hcty : uniformIndOccsE (ci.members.map (·.name)) (M.lps.map Level.param) ci.nP 0
      cc.type = true :=
    hun cc.type (List.mem_map_of_mem (List.mem_of_getElem? hcc))
  have hfield := uniformIndOccsE_stripPis (names := ci.members.map (·.name))
    (lvls := M.lps.map Level.param) (nP := ci.nP) (ci.nP + cc.nFields) hstrip hbd hcty
  rw [Nat.zero_add] at hfield
  rw [← Expr.mkAppN_getApp bd.1, hhead] at hfield
  obtain ⟨hus, -, hsp⟩ := uniformIndOccsE_spine
    (List.elem_eq_true_of_mem hT) hlen hfield
  refine ⟨hus, ?_⟩
  rw [hsp]
  simp only [structPsAt]
  refine List.map_congr_left fun i _ => ?_
  congr 1
  omega

/-- **The walk at the BODY of a peel** (task #315 L-B):
`uniformIndOccsE_stripPis`' twin at the residual — peeling `n` `Π`s
lands the walk `n` binders deeper on what is left.  This is what a
REFLEXIVE field's own telescope asks for: the member application sits
under the field's binders, not at the field's own depth. -/
theorem uniformIndOccsE_stripPis_res {names : List Name} {lvls : List Level} {nP : Nat} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {res : Expr} {o : Nat},
      e.stripPis n = some (bs, res) →
      uniformIndOccsE names lvls nP o e = true →
      uniformIndOccsE names lvls nP (o + n) res = true
  | 0, e, bs, res, o, h, hw => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simpa using hw
  | n + 1, e, bs, res, o, h, hw => by
    match e, h, hw with
    | .forallE ty b m, h, hw =>
      simp only [Expr.stripPis] at h
      cases hb : b.stripPis n with
      | none => rw [hb] at h; exact nomatch h
      | some r =>
        obtain ⟨bs₀, body₀⟩ := r
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨-, hbody⟩ := uniformIndOccsE_forallE_inv hw
        rw [show o + (n + 1) = o + 1 + n by omega]
        exact uniformIndOccsE_stripPis_res n hb hbody

/-- **A CONTAINER'S STORED REFLEXIVE FIELD SITS AT THE PARAMETER SPINE
UNDER ITS OWN BINDERS** (task #315 L-B): `nestedContainersOk_memberSpine`
at a field whose member application stands under `d` binders of the
field's own telescope — the walk is carried through the field's peel by
`uniformIndOccsE_stripPis_res`, so the parameter variables it finds are
`structPsAt (l + d) ci.nP`, the group's levels unchanged. -/
theorem nestedContainersOk_memberSpineRefl {env : Env} {pins : List NestedPin}
    (h : nestedContainersOk env pins = true)
    {q : NestedPin} (hq : q ∈ pins) {ci : ContainerInfo}
    (hci : containerInfo? env q.container = some ci)
    {M : ContainerMember} (hM : M ∈ ci.members)
    {j : Nat} {cc : ContainerCtor} (hcc : M.ctors[j]? = some cc)
    {bs : List (Expr × BinderMeta)} {res : Expr}
    (hstrip : cc.type.stripPis (ci.nP + cc.nFields) = some (bs, res))
    {l : Nat} {bd : Expr × BinderMeta} (hbd : bs[ci.nP + l]? = some bd)
    {d : Nat} {tbs : List (Expr × BinderMeta)} {body : Expr}
    (hpeel : bd.1.stripPis d = some (tbs, body))
    {T : Name} {us : List Level}
    (hhead : body.getAppFn = Expr.const T us)
    (hT : T ∈ ci.members.map (·.name))
    (hlen : ci.nP ≤ body.getAppArgs.length) :
    us = M.lps.map Level.param ∧
      body.getAppArgs.take ci.nP = ConLeche.structPsAt (l + d) ci.nP := by
  obtain ⟨-, hun⟩ := nestedContainersOk_uniform h hq hci hM
  have hcty : uniformIndOccsE (ci.members.map (·.name)) (M.lps.map Level.param) ci.nP 0
      cc.type = true :=
    hun cc.type (List.mem_map_of_mem (List.mem_of_getElem? hcc))
  have hfield := uniformIndOccsE_stripPis (names := ci.members.map (·.name))
    (lvls := M.lps.map Level.param) (nP := ci.nP) (ci.nP + cc.nFields) hstrip hbd hcty
  rw [Nat.zero_add] at hfield
  have hbody := uniformIndOccsE_stripPis_res (names := ci.members.map (·.name))
    (lvls := M.lps.map Level.param) (nP := ci.nP) d hpeel hfield
  rw [← Expr.mkAppN_getApp body, hhead] at hbody
  obtain ⟨hus, -, hsp⟩ := uniformIndOccsE_spine
    (List.elem_eq_true_of_mem hT) hlen hbody
  refine ⟨hus, ?_⟩
  rw [hsp]
  simp only [structPsAt]
  refine List.map_congr_left fun i _ => ?_
  congr 1
  omega

end ConLeche
