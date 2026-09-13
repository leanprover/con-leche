module

public import ConLeche.Verify.Inductives.NestedFacts

public section

/-!
# The elimination's PIN LEDGER: every copy's origin (task #279 M-B′ step 2b)

`NestedFacts.lean` records the elimination's NAMES; the fold spellings
of the model lane (`ψ_A` from a container's recursor, DESIGN §M.3) need
its CONTENT: which container's group a copy belongs to, at which level
instantiation and pins, at which position among its group, and that the
copy's constructors are the container's own — instantiated at the pins
by `mkCopy` and then rewritten in place by the worklist's
`elimCtors`.  Read off the definitions as one loop invariant:

* every state change of the elimination is a **mint** — one `mkCopies`
  call on the `containerInfo?` group of some stored inductive `I`
  (`MintStep`, the reflexive-transitive chain of such calls; the
  replace walks and `elimCtors` produce one, `replaceAllNested_mint`);
  a mint appends one type and one pin per group member
  (`mkCopies_spec`);
* the **origin** of pin `j` (`PinOriginAt`): the group, its base
  position `j₀` in the pin list (the whole group sits at `j₀ …`, in
  member order, all at one `lvls`/`Ds`), the pin's own record, the
  `mkCopy` record the copy was minted as, and the state of its
  constructors — RAW (the minted ones) while the worklist has not
  reached it, PROCESSED (`elimCtors` at some earlier states, whose pin
  lists are prefixes of the current one) once it has;
* the **ledger** (`ElimLedger`) holds of every pin and is preserved by
  mints (`ledger_mintStep`) and by the worklist's in-place `set`
  (`elimLoop_ledger`); at the loop's end every copy is processed
  (`elimNested_copy`).
-/

namespace ConLeche

/-! ## Mints -/

/-- A chain of `mkCopies` calls, each on a stored container's group. -/
inductive MintStep (env : Env) (nP : Nat) (pbs₀ : List (Expr × BinderMeta)) :
    ElimState → ElimState → Prop
  | refl (st : ElimState) : MintStep env nP pbs₀ st st
  | mint {st st' st'' : ElimState} {I : Name} {ci : ContainerInfo}
      {lvls : List Level} {Ds : List Expr} {got : Option Name} {base size : Nat}
      (hci : containerInfo? env I = some ci)
      (hmk : mkCopies env pbs₀ lvls Ds I base size ci.members st = .ok (st', got))
      (hDs : ∀ D ∈ Ds, D.looseBVarsBounded 0 = true)
      (hpbs : pbs₀.length = nP) (hDsLen : Ds.length = ci.nP)
      (hrest : MintStep env nP pbs₀ st' st'') : MintStep env nP pbs₀ st st''

theorem MintStep.trans {env : Env} {nP : Nat} {pbs₀ : List (Expr × BinderMeta)}
    {st₁ st₂ st₃ : ElimState}
    (h₁ : MintStep env nP pbs₀ st₁ st₂) (h₂ : MintStep env nP pbs₀ st₂ st₃) :
    MintStep env nP pbs₀ st₁ st₃ := by
  induction h₁ with
  | refl => exact h₂
  | mint hci hmk hDs hpbs hDsLen _ ih => exact .mint hci hmk hDs hpbs hDsLen (ih h₂)

/-- What one `mkCopies` call does: one copy per group member, appended
to the types, and one pin per member, appended to the pins, in member
order at one level instantiation and one pin list. -/
theorem mkCopies_spec {env : Env} {pbs : List (Expr × BinderMeta)} {lvls : List Level}
    {Ds : List Expr} {I : Name} {base size : Nat} :
    ∀ {members : List ContainerMember} {st st' : ElimState} {got : Option Name},
      mkCopies env pbs lvls Ds I base size members st = .ok (st', got) →
      ∃ copies : List AuxType, copies.length = members.length ∧
        st'.types = st.types ++ copies ∧
        st'.pins = st.pins ++ List.zipWith
          (fun (c : AuxType) (J : ContainerMember) =>
            (⟨c.name, J.name, Expr.mkAppN (.const J.name lvls) Ds, base, size⟩ : NestedPin))
          copies members ∧
        ∀ (i : Nat) (J : ContainerMember), members[i]? = some J →
          ∃ copy : AuxType, copies[i]? = some copy ∧ mkCopy pbs lvls Ds copy.name J = .ok copy
  | [], st, st', got, h => by
    simp only [mkCopies, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨[], rfl, by simp, by simp, fun i J h => nomatch h⟩
  | J :: rest, st, st', got, h => by
    simp only [mkCopies, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · next _ copy hcopy =>
      split at h
      · exact nomatch h
      · next _ q hq =>
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨copies, hlen, hty, hpin, hall⟩ := mkCopies_spec hq
        have hname := mkCopy_name hcopy
        refine ⟨copy :: copies, by simp [hlen], ?_, ?_, ?_⟩
        · rw [hty]; simp
        · rw [hpin]; simp [hname]
        · intro i J' hi
          cases i with
          | zero =>
            obtain rfl : J' = J := (Option.some.inj hi).symm
            exact ⟨copy, rfl, by rw [hname]; exact hcopy⟩
          | succ i => exact hall i J' hi

/-- A mint keeps the pin list as a prefix. -/
theorem MintStep.pins_prefix {env : Env} {nP : Nat} {pbs₀ : List (Expr × BinderMeta)}
    {st st' : ElimState} (h : MintStep env nP pbs₀ st st') : st.pins <+: st'.pins := by
  induction h with
  | refl => exact List.prefix_refl _
  | @mint s₁ s₂ s₃ _ _ _ _ _ _ _ _ hmk _ _ _ _ ih =>
    obtain ⟨copies, hlen, hty, hpin, hall⟩ := mkCopies_spec hmk
    have h₁ : s₁.pins <+: s₂.pins := by rw [hpin]; exact List.prefix_append _ _
    exact h₁.trans ih

/-- A nested occurrence's parameter arguments are bvar-closed (the
elimination's own rule: "nested inductive datatypes parameters cannot
contain local variables"). -/
theorem nestedOccOk_closed_of {I : Name} {names : List Name} {nP : Nat} {args : List Expr}
    {nested : Bool} (hocc : nestedOccOk I names nP args = .ok nested)
    (hn : ¬ ((!nested) = true)) : ∀ D ∈ args.take nP, D.looseBVarsBounded 0 = true := by
  have hnested : nested = true := by
    cases nested with
    | true => rfl
    | false => exact absurd rfl hn
  subst hnested
  unfold nestedOccOk at hocc
  try simp only at hocc
  split at hocc
  · exact nomatch hocc
  · next hne =>
    simp only [Except.ok.injEq] at hocc
    rw [hocc, Bool.true_and, Bool.not_eq_true, List.any_eq_false] at hne
    intro D hD
    have := hne D hD
    simpa using this

/-- `replaceIfNested` is a mint (or nothing). -/
theorem replaceIfNested_mint {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st : ElimState} {e : Expr}
    {r : Option (Expr × ElimState)} {nP : Nat} (hpbs : pbs.length = nP)
    (h : replaceIfNested env blvls params pbs st e = .ok r) :
    ∀ e' st', r = some (e', st') → MintStep env nP pbs st st' := by
  intro e' st' hr
  subst hr
  unfold replaceIfNested at h
  simp only [bind, Except.bind] at h
  repeat' (first | contradiction | split at h)
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    first
      | contradiction
      | (obtain ⟨-, rfl⟩ := h
         first
           | exact MintStep.refl _
           | exact MintStep.mint (by assumption) (by assumption)
               (nestedOccOk_closed_of (by assumption) (by assumption)) hpbs
               (by simp only [List.length_take]; omega) (MintStep.refl _))

/-- The top-down replace is a chain of mints. -/
theorem replaceAllNested_mint {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {nP : Nat} (hpbs : pbs.length = nP) :
    ∀ (e : Expr) {st : ElimState} {r : Expr × ElimState},
      replaceAllNested env blvls params pbs st e = .ok r → MintStep env nP pbs st r.2 := by
  intro e
  induction e with
  | bvar i =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact MintStep.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mint hpbs hr' _ _ rfl
      · obtain rfl := Except.ok.inj h
        exact MintStep.refl _
  | fvar idx ty _ =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact MintStep.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mint hpbs hr' _ _ rfl
      · obtain rfl := Except.ok.inj h
        exact MintStep.refl _
  | sort u =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact MintStep.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mint hpbs hr' _ _ rfl
      · obtain rfl := Except.ok.inj h
        exact MintStep.refl _
  | const n us =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact MintStep.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mint hpbs hr' _ _ rfl
      · obtain rfl := Except.ok.inj h
        exact MintStep.refl _
  | lit l =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact MintStep.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mint hpbs hr' _ _ rfl
      · obtain rfl := Except.ok.inj h
        exact MintStep.refl _
  | app f a ihf iha =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact MintStep.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mint hpbs hr' _ _ rfl
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            show MintStep env nP pbs st st₂
            exact (ihf h₁).trans (iha h₂)
  | lam ty b bm ihty ihb =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact MintStep.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mint hpbs hr' _ _ rfl
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            show MintStep env nP pbs st st₂
            exact (ihty h₁).trans (ihb h₂)
  | forallE ty b bm ihty ihb =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact MintStep.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mint hpbs hr' _ _ rfl
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            show MintStep env nP pbs st st₂
            exact (ihty h₁).trans (ihb h₂)
  | letE ty v b ihty ihv ihb =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact MintStep.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mint hpbs hr' _ _ rfl
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            split at h
            · contradiction
            · next x₃ st₃ h₃ =>
              obtain rfl := Except.ok.inj h
              show MintStep env nP pbs st st₃
              exact ((ihty h₁).trans (ihv h₂)).trans (ihb h₃)
  | proj s i x ihx =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact MintStep.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mint hpbs hr' _ _ rfl
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          obtain rfl := Except.ok.inj h
          show MintStep env nP pbs st st₁
          exact ihx h₁



/-- A mint keeps the type list as a prefix. -/
theorem mintStep_types_prefix {env : Env} {nP : Nat} {pbs₀ : List (Expr × BinderMeta)}
    {st st' : ElimState} (h : MintStep env nP pbs₀ st st') : st.types <+: st'.types := by
  induction h with
  | refl => exact List.prefix_refl _
  | @mint s₁ s₂ s₃ _ _ _ _ _ _ _ _ hmk _ _ _ _ ih =>
    obtain ⟨copies, hlen, hty, hpin, hall⟩ := mkCopies_spec hmk
    have h₁ : s₁.types <+: s₂.types := by rw [hty]; exact List.prefix_append _ _
    exact h₁.trans ih

/-- A stripped telescope has exactly `n` binders. -/
theorem stripPis_length' : ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
    e.stripPis n = some (bs, body) → bs.length = n
  | 0, _, bs, _, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | n + 1, e, bs, body, h => by
    match e, h with
    | .forallE ty b m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₀, r₀⟩, h₀, h₁⟩ := h
      simp only [Prod.mk.injEq] at h₁
      rw [← h₁.1, List.length_cons, stripPis_length' n h₀]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => simp [Expr.stripPis] at h

/-- One type's constructors rewritten: a chain of mints. -/
theorem elimCtors_mint {env : Env} {blvls : List Level} {nP : Nat} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} (hpbs : pbs₀.length = nP) :
    ∀ {cs : List (Name × Expr × Nat)} {st : ElimState}
      {r : List (Name × Expr × Nat) × ElimState},
      elimCtors env blvls nP params pbs₀ cs st = .ok r → MintStep env nP pbs₀ st r.2
  | [], st, r, h => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact MintStep.refl st
  | (c, cty, nF) :: rest, st, r, h => by
    simp only [elimCtors, bind, Except.bind] at h
    split at h
    · split at h
      · split at h
        · contradiction
        · next q st₁ hq =>
          split at h
          · contradiction
          · next rest' st₂ hrest =>
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            have h₁ := replaceAllNested_mint hpbs _ hq
            have h₂ := elimCtors_mint hpbs hrest
            exact h₁.trans h₂
      · contradiction
    · contradiction

/-! ## The ledger -/

/-- **The origin of pin `j`** in a state, with the worklist at `qhead`
(see the module docstring): `k` is the block's own type count, so the
copy's type sits at `k + j`. -/
def PinOriginAt (env : Env) (k : Nat) (blvls : List Level) (nP : Nat) (params : List Expr)
    (pbs : List (Expr × BinderMeta)) (st : ElimState) (qhead j : Nat) : Prop :=
  ∃ (I : Name) (ci : ContainerInfo) (i j₀ : Nat) (J : ContainerMember) (lvls : List Level)
    (Ds : List Expr) (q : NestedPin) (copy t : AuxType),
    containerInfo? env I = some ci ∧ ci.members[i]? = some J ∧ j = j₀ + i ∧
    (∀ i' J', ci.members[i']? = some J' →
      ∃ q', st.pins[j₀ + i']? = some q' ∧ q'.container = J'.name ∧
        q'.pin = Expr.mkAppN (.const J'.name lvls) Ds) ∧
    st.pins[j]? = some q ∧ q.container = J.name ∧ q.pin = Expr.mkAppN (.const J.name lvls) Ds ∧
    mkCopy pbs lvls Ds q.aux J = .ok copy ∧
    (∀ D ∈ Ds, D.looseBVarsBounded 0 = true) ∧ pbs.length = nP ∧ Ds.length = ci.nP ∧
    st.types[k + j]? = some t ∧ t.name = copy.name ∧ t.type = copy.type ∧
    (qhead ≤ k + j → t.ctors = copy.ctors) ∧
    (k + j < qhead → ∃ (st₁ st₂ : ElimState) (cs' : List (Name × Expr × Nat)),
      elimCtors env blvls nP params pbs copy.ctors st₁ = .ok (cs', st₂) ∧ t.ctors = cs' ∧
      st₁.pins <+: st.pins ∧ st₂.pins <+: st.pins)

/-- **The ledger**: the types are the block's `k` followed by one per
pin, and every pin has an origin. -/
def ElimLedger (env : Env) (k : Nat) (blvls : List Level) (nP : Nat) (params : List Expr)
    (pbs : List (Expr × BinderMeta)) (st : ElimState) (qhead : Nat) : Prop :=
  st.types.length = k + st.pins.length ∧
  ∀ j, j < st.pins.length → PinOriginAt env k blvls nP params pbs st qhead j

/-- An origin survives an extension of the state that keeps the pins
as a prefix and the types as a prefix. -/
theorem PinOriginAt.mono {env : Env} {k : Nat} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {qhead j : Nat}
    (h : PinOriginAt env k blvls nP params pbs st qhead j)
    (hp : st.pins <+: st'.pins) (ht : st.types <+: st'.types) :
    PinOriginAt env k blvls nP params pbs st' qhead j := by
  obtain ⟨I, ci, i, j₀, J, lvls, Ds, q, copy, t, hci, hJ, hj, hgrp, hq, hqc, hqp, hmk, hDs, hpbs, hDsLen, ht',
    hn, hty, hraw, hproc⟩ := h
  have hpins : ∀ {i : Nat} {q : NestedPin}, st.pins[i]? = some q → st'.pins[i]? = some q := by
    intro i q hq'
    obtain ⟨tl, htl⟩ := hp
    rw [← htl, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hq').1]
    exact hq'
  refine ⟨I, ci, i, j₀, J, lvls, Ds, q, copy, t, hci, hJ, hj, fun i' J' hi' => ?_,
    hpins hq, hqc, hqp, hmk, hDs, hpbs, hDsLen, ?_, hn, hty, hraw, fun hlt => ?_⟩
  · obtain ⟨q', hq', hc', hp'⟩ := hgrp i' J' hi'
    exact ⟨q', hpins hq', hc', hp'⟩
  · obtain ⟨tl, htl⟩ := ht
    rw [← htl, List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht').1]
    exact ht'
  · obtain ⟨st₁, st₂, cs', hrun, hcs, h₁, h₂⟩ := hproc hlt
    exact ⟨st₁, st₂, cs', hrun, hcs, h₁.trans hp, h₂.trans hp⟩

/-- A mint of one group at a state the worklist has not passed keeps
the ledger: the old pins' origins are unchanged and the new ones are
raw, at the group's base position. -/
theorem ledger_mint {env : Env} {k : Nat} {blvls : List Level} {nP : Nat} {params : List Expr}
    {st st' : ElimState} {qhead : Nat} {I : Name} {ci : ContainerInfo}
    {pbs : List (Expr × BinderMeta)} {lvls : List Level} {Ds : List Expr} {got : Option Name}
    {base size : Nat}
    (hci : containerInfo? env I = some ci)
    (hmk : mkCopies env pbs lvls Ds I base size ci.members st = .ok (st', got))
    (hDs : ∀ D ∈ Ds, D.looseBVarsBounded 0 = true) (hpbs : pbs.length = nP)
    (hDsLen : Ds.length = ci.nP)
    (hL : ElimLedger env k blvls nP params pbs st qhead) (hq : qhead ≤ st.types.length) :
    ElimLedger env k blvls nP params pbs st' qhead := by
  obtain ⟨hlen, hall⟩ := hL
  obtain ⟨copies, hclen, hty, hpin, hcopies⟩ := mkCopies_spec hmk
  have hzlen : (List.zipWith (fun (c : AuxType) (J : ContainerMember) =>
      (⟨c.name, J.name, Expr.mkAppN (.const J.name lvls) Ds, base, size⟩ : NestedPin))
        copies ci.members).length
      = copies.length := by
    rw [List.length_zipWith, hclen, Nat.min_self]
  refine ⟨by rw [hty, hpin, List.length_append, List.length_append, hzlen, hlen]; omega,
    fun j hj => ?_⟩
  rw [hpin, List.length_append, hzlen] at hj
  rcases Nat.lt_or_ge j st.pins.length with hlt | hge
  · exact (hall j hlt).mono (by rw [hpin]; exact List.prefix_append _ _)
      (by rw [hty]; exact List.prefix_append _ _)
  · -- a new pin: member `i := j - st.pins.length` of the group
    obtain ⟨i, rfl⟩ : ∃ i, j = st.pins.length + i := ⟨j - st.pins.length, by omega⟩
    have hi : i < copies.length := by omega
    obtain ⟨copy, hcopy⟩ : ∃ copy, copies[i]? = some copy := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨J, hJ⟩ : ∃ J, ci.members[i]? = some J :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hclen]; exact hi)⟩
    obtain ⟨copy', hcopy', hmkc⟩ := hcopies i J hJ
    obtain rfl : copy = copy' := Option.some.inj (hcopy.symm.trans hcopy')
    have hpinAt : ∀ i' J', ci.members[i']? = some J' →
        st'.pins[st.pins.length + i']? = some
          ⟨(copies.getD i' default).name, J'.name, Expr.mkAppN (.const J'.name lvls) Ds,
            base, size⟩ := by
      intro i' J' hi'
      have hi'l : i' < copies.length := by
        rw [hclen]; exact (List.getElem?_eq_some_iff.mp hi').1
      rw [hpin, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        List.getElem?_zipWith, hi', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'l]
      rfl
    refine ⟨I, ci, i, st.pins.length, J, lvls, Ds,
      ⟨copy.name, J.name, Expr.mkAppN (.const J.name lvls) Ds, base, size⟩, copy, copy, hci, hJ, rfl,
      fun i' J' hi' => ⟨_, hpinAt i' J' hi', rfl, rfl⟩, ?_, rfl, rfl, hmkc, hDs, hpbs, hDsLen, ?_, rfl, rfl,
      fun _ => rfl, fun hlt => ?_⟩
    · have := hpinAt i J hJ
      rw [List.getD_eq_getElem?_getD, hcopy] at this
      exact this
    · rw [hty, List.getElem?_append_right (by omega), show k + (st.pins.length + i) - st.types.length
        = i by omega]
      exact hcopy
    · exfalso; omega

/-- The ledger survives a chain of mints. -/
theorem ledger_mintStep {env : Env} {k : Nat} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {qhead : Nat}
    (h : MintStep env nP pbs st st') (hL : ElimLedger env k blvls nP params pbs st qhead)
    (hq : qhead ≤ st.types.length) : ElimLedger env k blvls nP params pbs st' qhead := by
  induction h with
  | refl => exact hL
  | mint hci hmk hDs hpbs hDsLen _ ih =>
    have hL' := ledger_mint hci hmk hDs hpbs hDsLen hL hq
    refine ih hL' ?_
    obtain ⟨copies, hlen, hty, hpin, hall⟩ := mkCopies_spec hmk
    rw [hty, List.length_append]; omega

/-- **The worklist keeps the ledger**: a step processes the copy at
`qhead` (raw before, processed after, at the states around its
`elimCtors`) and touches no other entry. -/
theorem elimLoop_ledger {env : Env} {k : Nat} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs : List (Expr × BinderMeta)} (hpbs : pbs.length = nP) :
    ∀ {fuel qhead : Nat} {st st' : ElimState},
      elimLoop env blvls nP params pbs fuel qhead st = .ok st' →
      ElimLedger env k blvls nP params pbs st qhead →
      ElimLedger env k blvls nP params pbs st' st'.types.length
  | 0, _, _, _, h, _ => nomatch h
  | fuel + 1, qhead, st, st', h, hL => by
    simp only [elimLoop] at h
    split at h
    · next hnone =>
      obtain rfl := Except.ok.inj h
      -- the worklist is past the end: every entry is processed
      have hge : st.types.length ≤ qhead := by
        refine Classical.byContradiction fun hlt => ?_
        rw [List.getElem?_eq_getElem (Nat.lt_of_not_le hlt)] at hnone
        exact nomatch hnone
      obtain ⟨hlen, hall⟩ := hL
      refine ⟨hlen, fun j hj => ?_⟩
      obtain ⟨I, ci, i, j₀, J, lvls, Ds, q, copy, t, hci, hJ, hjE, hgrp, hq, hqc, hqp, hmk,
        hDs, hpbs', hDsLen, ht, hn, hty, hraw, hproc⟩ := hall j hj
      refine ⟨I, ci, i, j₀, J, lvls, Ds, q, copy, t, hci, hJ, hjE, hgrp, hq, hqc, hqp, hmk,
        hDs, hpbs', hDsLen, ht, hn, hty, fun hle => ?_, fun _ => hproc (by omega)⟩
      exfalso; omega
    · next t ht =>
      split at h
      · exact nomatch h
      · next cs' st₁ hcs =>
        have hqlt : qhead < st.types.length := (List.getElem?_eq_some_iff.mp ht).1
        have hmint := elimCtors_mint hpbs hcs
        have hL₁ : ElimLedger env k blvls nP params pbs st₁ qhead :=
          ledger_mintStep hmint hL (Nat.le_of_lt hqlt)
        have hpre : st.pins <+: st₁.pins := hmint.pins_prefix
        -- the ledger after the `set`, at `qhead + 1`
        have hL₂ : ElimLedger env k blvls nP params pbs
            { st₁ with types := st₁.types.set qhead { t with ctors := cs' } } (qhead + 1) := by
          obtain ⟨hlen₁, hall₁⟩ := hL₁
          refine ⟨by simp [hlen₁], fun j hj => ?_⟩
          have hj' : j < st₁.pins.length := hj
          obtain ⟨I, ci, i, j₀, J, lvls, Ds, q, copy, t', hci, hJ, hjE, hgrp, hq, hqc, hqp,
            hmk, hDs, hpbs', hDsLen, ht', hn, hty, hraw, hproc⟩ := hall₁ j hj
          by_cases hjq : k + j = qhead
          · -- the processed entry: it was raw at `st`, and `st` is the
            -- state its `elimCtors` ran from
            have htj : st.types[qhead]? = some t := ht
            have hraw' := hraw (Nat.le_of_eq hjq.symm)
            -- `t` is the entry at `st`, `t'` the same entry carried to `st₁`
            have htt : t = t' := by
              have hlt : qhead < st.types.length := hqlt
              obtain ⟨tl, htl⟩ := mintStep_types_prefix hmint
              rw [hjq, ← htl, List.getElem?_append_left hlt] at ht'
              exact Option.some.inj (htj.symm.trans ht')
            subst htt
            refine ⟨I, ci, i, j₀, J, lvls, Ds, q, copy, { t with ctors := cs' }, hci, hJ, hjE,
              hgrp, hq, hqc, hqp, hmk, hDs, hpbs', hDsLen, ?_, hn, hty, fun hle => ?_, fun _ => ?_⟩
            · show (st₁.types.set qhead { t with ctors := cs' })[k + j]? = some _
              rw [hjq, List.getElem?_set_self (by rw [hlen₁]; omega)]
            · exfalso; omega
            · refine ⟨st, st₁, cs', ?_, rfl, hpre, List.prefix_refl _⟩
              rw [← hraw']; exact hcs
          · refine ⟨I, ci, i, j₀, J, lvls, Ds, q, copy, t', hci, hJ, hjE, hgrp, hq, hqc, hqp,
              hmk, hDs, hpbs', hDsLen, ?_, hn, hty, fun hle => hraw (by omega),
              fun hlt => hproc (by omega)⟩
            show (st₁.types.set qhead { t with ctors := cs' })[k + j]? = some t'
            rw [List.getElem?_set_ne (fun h => hjq h.symm)]
            exact ht'
        exact elimLoop_ledger hpbs h hL₂

/-- **Every copy's origin, at the elimination's end**: pin `j` was
minted as member `i` of the `containerInfo?` group of a stored
inductive, whose whole group sits at `j₀ = j - i` in the pin list at one
level instantiation and one pin list; the copy's type is its `mkCopy`
record with its constructors rewritten by `elimCtors` at states whose
pin lists are prefixes of the final one; the block's parameters are the
first type's, opened at the free variables `0 … nP-1`. -/
theorem elimNested_copy {env : Env} {nP : Nat} {lps : List Name} {types : List AuxType}
    {st : ElimState} (h : elimNested env nP lps types = .ok st) {j : Nat}
    (hj : j < st.pins.length) :
    ∃ (t₀ : AuxType) (params : List Expr) (body : Expr) (pbs : List (Expr × BinderMeta))
      (body₀ : Expr),
      types.head? = some t₀ ∧ openPisAtFvars nP t₀.type 0 = some (params, body) ∧
      t₀.type.stripPis nP = some (pbs, body₀) ∧
      ∃ (I : Name) (ci : ContainerInfo) (i j₀ : Nat) (J : ContainerMember) (lvls : List Level)
        (Ds : List Expr) (q : NestedPin) (copy : AuxType)
        (st₁ st₂ : ElimState) (cs' : List (Name × Expr × Nat)),
        containerInfo? env I = some ci ∧ ci.members[i]? = some J ∧ j = j₀ + i ∧
        (∀ i' J', ci.members[i']? = some J' →
          ∃ q', st.pins[j₀ + i']? = some q' ∧ q'.container = J'.name ∧
            q'.pin = Expr.mkAppN (.const J'.name lvls) Ds) ∧
        st.pins[j]? = some q ∧ q.container = J.name ∧
        q.pin = Expr.mkAppN (.const J.name lvls) Ds ∧
        mkCopy pbs lvls Ds q.aux J = .ok copy ∧
        (∀ D ∈ Ds, D.looseBVarsBounded 0 = true) ∧ pbs.length = nP ∧ Ds.length = ci.nP ∧
        st.types[types.length + j]? = some { copy with ctors := cs' } ∧
        elimCtors env (lps.map Level.param) nP params pbs copy.ctors st₁ = .ok (cs', st₂) ∧
        st₁.pins <+: st.pins ∧ st₂.pins <+: st.pins := by
  unfold elimNested at h
  split at h
  · next t₀ ht₀ =>
    split at h
    · next params body hop =>
      split at h
      · next pbs body₀ hstrip =>
        have hpbs : pbs.length = nP := stripPis_length' nP hstrip
        have hL₀ : ElimLedger env types.length (lps.map Level.param) nP params pbs ⟨types, [], 1⟩ 0 :=
          ⟨by simp, fun j hj => nomatch hj⟩
        obtain ⟨hlen, hall⟩ := elimLoop_ledger hpbs h hL₀
        obtain ⟨I, ci, i, j₀, J, lvls, Ds, q, copy, t, hci, hJ, hjE, hgrp, hq, hqc, hqp, hmk,
          hDs, -, hDsLen, ht, hn, hty, -, hproc⟩ := hall j hj
        obtain ⟨st₁, st₂, cs', hrun, hcs, h₁, h₂⟩ := hproc (by omega)
        refine ⟨t₀, params, body, pbs, body₀, ht₀, hop, hstrip, I, ci, i, j₀, J, lvls, Ds, q, copy,
          st₁, st₂, cs', hci, hJ, hjE, hgrp, hq, hqc, hqp, hmk, hDs, hpbs, hDsLen, ?_, hrun, h₁, h₂⟩
        rw [ht]
        congr 1
        cases t with
        | mk n ty cs =>
          cases copy with
          | mk n' ty' cs'' =>
            simp only at hn hty hcs
            subst hn hty hcs
            rfl
      · contradiction
    · contradiction
  · contradiction

/-! ## The replace walk, at a nested occurrence

Where `replaceIfNested` FIRES, the walk is its answer (the top-down
discipline), and that answer is the copy's carrier at the block's
parameters and the occurrence's index arguments — with the copy's
name recorded in a pin whose `pin` is the occurrence's head applied to
its PARAMETER arguments.  This is the ledger's side of a field's
rewrite. -/

/-- The container's own copy is pinned: the aux name `mkCopies`
returns is the one minted for `I` itself, and its pin is `I` at the
pin arguments. -/
theorem mkCopies_got {env : Env} {pbs : List (Expr × BinderMeta)} {lvls : List Level}
    {Ds : List Expr} {I : Name} {base size : Nat} :
    ∀ {members : List ContainerMember} {st st' : ElimState} {aux : Name},
      mkCopies env pbs lvls Ds I base size members st = .ok (st', some aux) →
      (⟨aux, I, Expr.mkAppN (.const I lvls) Ds, base, size⟩ : NestedPin) ∈ st'.pins
  | [], st, st', aux, h => by
    simp only [mkCopies, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact nomatch h.2
  | J :: rest, st, st', aux, h => by
    simp only [mkCopies, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · next copy hcopy =>
      split at h
      · exact nomatch h
      · next q hq =>
        obtain ⟨stq, gotq⟩ := q
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, hgot⟩ := h
        split at hgot
        · next hJI =>
          obtain rfl : J.name = I := beq_iff_eq.mp hJI
          obtain rfl := (Option.some.inj hgot).symm
          obtain ⟨copies, -, -, hpin, -⟩ := mkCopies_spec hq
          rw [hpin]
          refine List.mem_append_left _ ?_
          simp
        · obtain rfl := hgot
          exact mkCopies_got hq

/-- **A fired replacement, read off**: the node is a container's
application, and the walk's answer is the copy at the block's
parameters and the occurrence's index arguments, with the copy's pin in
the resulting state. -/
theorem replaceIfNested_some {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {e r : Expr}
    (h : replaceIfNested env blvls params pbs st e = .ok (some (r, st'))) :
    ∃ (I : Name) (lvls : List Level) (ci : ContainerInfo) (aux : Name),
      containerInfo? env I = some ci ∧ ci.nP ≤ e.getAppArgs.length ∧
      e = Expr.mkAppN (.const I lvls) e.getAppArgs ∧
      r = Expr.mkAppN (Expr.mkAppN (.const aux blvls) params) (e.getAppArgs.drop ci.nP) ∧
      ∃ q ∈ st'.pins, q.aux = aux ∧
        q.pin = Expr.mkAppN (.const I lvls) (e.getAppArgs.take ci.nP) := by
  unfold replaceIfNested at h
  simp only [bind, Except.bind] at h
  split at h
  · -- `e` is an application
    split at h
    · -- its head is a constant
      next I lvls hfn =>
      split at h
      · -- a stored inductive
        split at h
        · exact nomatch h
        · split at h
          · split at h
            · exact nomatch h
            · exact nomatch h
          · next ci hci =>
            split at h
            · exact nomatch h
            · next hnP =>
              split at h
              · exact nomatch h
              · next nested hocc =>
                split at h
                · exact nomatch h
                · split at h
                  · -- the pin is already in the table
                    next q hq =>
                    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    have hfind := List.find?_some hq
                    rw [beq_iff_eq] at hfind
                    refine ⟨I, lvls, ci, q.aux, hci, by omega, ?_, rfl,
                      q, List.mem_of_find?_eq_some hq, rfl, hfind⟩
                    rw [← hfn]; exact (Expr.mkAppN_getApp _).symm
                  · -- the group is minted here
                    split at h
                    · exact nomatch h
                    · next p hmk =>
                      obtain ⟨stq, gotq⟩ := p
                      split at h
                      · exact nomatch h
                      · next auxI hgot =>
                        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                          Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        obtain rfl := hgot
                        refine ⟨I, lvls, ci, auxI, hci, by omega, ?_, rfl,
                          _, mkCopies_got hmk, rfl, rfl⟩
                        rw [← hfn]; exact (Expr.mkAppN_getApp _).symm
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- **The walk at an application**: either the replacement fired at the
node — and then the walk IS its answer (the top-down discipline) — or
the head and the argument were walked in turn. -/
theorem replaceAllNested_app {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {f a r : Expr}
    (h : replaceAllNested env blvls params pbs st (.app f a) = .ok (r, st')) :
    replaceIfNested env blvls params pbs st (.app f a) = .ok (some (r, st')) ∨
      ∃ (f' a' : Expr) (st₁ : ElimState),
        replaceAllNested env blvls params pbs st f = .ok (f', st₁) ∧
          replaceAllNested env blvls params pbs st₁ a = .ok (a', st') ∧ r = .app f' a' := by
  rw [replaceAllNested] at h
  split at h
  · next hpr =>
    simp only [Bool.not_eq_true', List.any_eq_false] at hpr
    have hf : st.newNames.any (fun T => f.mentionsConst T) = false := by
      rw [List.any_eq_false]
      intro T hT
      have := hpr T hT
      simp only [Expr.mentionsConst, Bool.or_eq_true, not_or, Bool.not_eq_true] at this
      simp [this.1]
    have ha : st.newNames.any (fun T => a.mentionsConst T) = false := by
      rw [List.any_eq_false]
      intro T hT
      have := hpr T hT
      simp only [Expr.mentionsConst, Bool.or_eq_true, not_or, Bool.not_eq_true] at this
      simp [this.2]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨f, a, st, replaceAllNested_prune hf, replaceAllNested_prune ha, rfl⟩
  · split at h
    · exact nomatch h
    · next p hp =>
      obtain rfl := Except.ok.inj h
      exact Or.inl hp
    · split at h
      · exact nomatch h
      · next f' st₁ hf =>
        split at h
        · exact nomatch h
        · next a' st₂ ha =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr ⟨f', a', st₁, hf, ha, rfl⟩

/-! ## The copy's record, and the rewritten constructors -/

/-- A successful `mapM` in `Except`, positionally, with its length. -/
theorem exceptMapM_getElem? {α β : Type} {f : α → Except CheckError β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r →
      r.length = l.length ∧ ∀ (i : Nat) (a : α), l[i]? = some a →
        ∃ b, r[i]? = some b ∧ f a = .ok b
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i a h => nomatch h⟩
  | a :: rest, r, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · next b hb =>
      split at h
      · exact nomatch h
      · next rest' hrest =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hlen, hall⟩ := exceptMapM_getElem? hrest
        refine ⟨by simp [hlen], fun i a' hi => ?_⟩
        cases i with
        | zero => exact ⟨b, rfl, by rw [← Option.some.inj hi]; exact hb⟩
        | succ i => exact hall i a' hi

/-- **The copy's record**: its type and constructors are the container
member's, at the level instantiation, with the container's parameters
instantiated at the pins (`instPis`) and closed over the block's
parameter binders (`closeTelescope pbs 0`); the constructor names are
re-prefixed to the copy. -/
theorem mkCopy_inv {pbs : List (Expr × BinderMeta)} {lvls : List Level} {Ds : List Expr}
    {auxName : Name} {J : ContainerMember} {copy : AuxType}
    (h : mkCopy pbs lvls Ds auxName J = .ok copy) :
    lvls.length = J.lps.length ∧
    (∃ tyI, Expr.instPis (Expr.instantiateLevelParams J.lps lvls J.type) Ds = some tyI ∧
      copy.type = closeTelescope pbs 0 tyI) ∧
    copy.ctors.length = J.ctors.length ∧
    ∀ (l : Nat) (c : ContainerCtor), J.ctors[l]? = some c →
      ∃ cI, Expr.instPis (Expr.instantiateLevelParams J.lps lvls c.type) Ds = some cI ∧
        copy.ctors[l]? = some (Name.replacePrefix J.name auxName c.name, closeTelescope pbs 0 cI,
          c.nFields) := by
  unfold mkCopy at h
  try simp only [bind, Except.bind] at h
  repeat' (first | contradiction | split at h)
  all_goals
    try simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlenC, hall⟩ := exceptMapM_getElem? ‹List.mapM _ J.ctors = Except.ok _›
    refine ⟨beq_iff_eq.mp ‹_›, ⟨_, ‹_›, rfl⟩, hlenC, fun l c hc => ?_⟩
    obtain ⟨b, hb, hf⟩ := hall l c hc
    try simp only [bind, Except.bind] at hf
    split at hf
    · next cI hcI =>
      simp only [pure, Except.pure, Except.ok.injEq] at hf
      subst hf
      exact ⟨cI, hcI, hb⟩
    · exact nomatch hf

/-- **The rewritten constructors**, one by one: constructor `l`'s
parameter prefix is stripped (`stripPis`), its residual opened at the
block's parameter variables (`instPis`), rewritten by
`replaceAllNested` at a state between the run's start and end (pins as
prefixes), and closed again over its own binders. -/
theorem elimCtors_getElem? {env : Env} {blvls : List Level} {nP : Nat} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} (hpbs : pbs₀.length = nP) :
    ∀ {cs : List (Name × Expr × Nat)} {st : ElimState}
      {cs' : List (Name × Expr × Nat)} {st' : ElimState},
      elimCtors env blvls nP params pbs₀ cs st = .ok (cs', st') →
      cs'.length = cs.length ∧
      ∀ (l : Nat) (c : Name) (cty : Expr) (nF : Nat), cs[l]? = some (c, cty, nF) →
        ∃ (pbs : List (Expr × BinderMeta)) (rest cbody body' : Expr) (sta stb : ElimState),
          cty.stripPis nP = some (pbs, rest) ∧ Expr.instPis cty params = some cbody ∧
          replaceAllNested env blvls params pbs₀ sta cbody = .ok (body', stb) ∧
          cs'[l]? = some (c, closeTelescope pbs 0 body', nF) ∧
          st.pins <+: sta.pins ∧ stb.pins <+: st'.pins
  | [], st, cs', st', h => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun l c cty nF h => nomatch h⟩
  | (c, cty, nF) :: rest, st, cs', st', h => by
    simp only [elimCtors, bind, Except.bind] at h
    split at h
    · next pbs rest₀ hstrip =>
      split at h
      · next cbody hinst =>
        split at h
        · contradiction
        · next q st₁ hq =>
          split at h
          · contradiction
          · next rest' st₂ hrest =>
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hlen, hall⟩ := elimCtors_getElem? hpbs hrest
            have hp₁ : st.pins <+: st₁.2.pins :=
              (replaceAllNested_mint hpbs _ hq).pins_prefix
            have hp₂ : st₁.2.pins <+: st₂.2.pins := (elimCtors_mint hpbs hrest).pins_prefix
            refine ⟨by simp [hlen], fun l c' cty' nF' hl => ?_⟩
            cases l with
            | zero =>
              obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hl)
              obtain ⟨h3, h4⟩ := Prod.mk.inj h2
              subst h1 h3 h4
              exact ⟨pbs, rest₀, cbody, st₁.1, st, st₁.2, hstrip, hinst, hq, rfl,
                List.prefix_refl _, hp₂⟩
            | succ l =>
              obtain ⟨pbs', rest₁, cbody', body', sta, stb, h1, h2, h3, h4, h5, h6⟩ :=
                hall l c' cty' nF' hl
              exact ⟨pbs', rest₁, cbody', body', sta, stb, h1, h2, h3, h4, hp₁.trans h5, h6⟩
      · contradiction
    · contradiction

end ConLeche
