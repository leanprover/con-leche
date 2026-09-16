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
