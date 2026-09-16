module

public import ConLeche.Kernel.Inductives.NestedInstall
import ConLeche.Verify.Inductives.MutualInv

public section

/-!
# The nested elimination, inverted (task #315)

Two readings of the pure elimination
(`ConLeche/Kernel/Inductives/NestedElim.lean`) that the model tier needs
and no other Verify module provides.

* **The count.**  Every mint appends ONE type and ONE pin, in the same
  breath (`mkCopies`), and nothing else in the elimination changes
  either length — `replaceIfNested` either passes the state through or
  mints, `replaceAllNested` only threads, `elimCtors` only threads and
  `elimLoop` `set`s a type in place.  So the elimination's type list is
  the input list plus one type per pin: `elimNested_types_length`.  With
  `nestedTypes0_length`, `nestedAnnotFormers_length` and `auxBlock_k`
  that is the auxiliary block's member count, `p.k + st.pins.length`.
  The per-function lemmas are stated additively
  (`st'.types.length + st.pins.length = st.types.length + st'.pins.length`)
  so that no subtraction has to be justified along the chain.
* **The copy record, inverted.**  `nestedCopySrcOk`
  (`ConLeche/Kernel/Inductives/NestedInstall.lean`, K.28) is a Bool over
  the pin range; `nestedCopySrcOk_inv` turns it into the per-pin package
  the model reads — the source field, the pin's spelling, the container
  lookup, and `mkCopy`'s output at that source agreeing with the stored
  type — and `mkCopy_inv` reads that output's components off `mkCopy`
  itself.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- An `.error` never succeeds. -/
private theorem elimErr_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (Except.error e : CheckM α) = .ok a) : False := by
  simp at h

/-- A declining step never returns a replacement. -/
private theorem elimNone_ne_some {α : Type} {a : α}
    (h : (pure none : CheckM (Option α)) = .ok (some a)) : False := by
  simp [pure, Except.pure] at h

/-- Close a branch the run cannot have taken (`NestedInv.lean`'s
tactic, at this file's two failing shapes: the elimination is a plain
`Except`, so its refusals are `.error`s rather than `throw`s). -/
local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact elimErr_ne_ok (by assumption))
        | (exfalso; exact elimNone_ne_some (by assumption)))

/-! ## (A) The elimination's count -/

/-- A successful `mapM` in `Option` yields as many results. -/
theorem mapM_option_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨b, -, bs, hbs, rfl⟩ := h
    simp [mapM_option_length hbs]

/-- **One mint group**: `mkCopies` appends one type and one pin per
member it copies, so the difference of the two lengths is unchanged. -/
theorem mkCopies_lengths {env : Env} {pbs : List (Expr × BinderMeta)}
    {lvls : List Level} {Ds : List Expr} {I : Name} {base size : Nat} :
    ∀ {Js : List ContainerMember} {st st' : ElimState} {got : Option Name},
      mkCopies env pbs lvls Ds I base size Js st = .ok (st', got) →
      st'.types.length + st.pins.length = st.types.length + st'.pins.length
  | [], st, st', got, h => by
    simp only [mkCopies, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    omega
  | J :: rest, st, st', got, h => by
    rw [mkCopies] at h
    split at h
    obtain ⟨copy, -, h⟩ := exceptBind_ok h
    obtain ⟨q, hrec, h⟩ := exceptBind_ok h
    obtain ⟨stM, gotM⟩ := q
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have ih := mkCopies_lengths hrec
    simp only [List.length_append, List.length_cons, List.length_nil] at ih
    omega

/-- **One occurrence**: `replaceIfNested` either passes the state
through or mints exactly one group. -/
theorem replaceIfNested_lengths {env : Env} {blvls : List Level} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} {st st' : ElimState} {e e' : Expr}
    (h : replaceIfNested env blvls params pbs₀ st e = .ok (some (e', st'))) :
    st'.types.length + st.pins.length = st.types.length + st'.pins.length := by
  unfold replaceIfNested at h
  split at h
  · split at h
    · split at h
      · split at h
        · close_throw
        · split at h
          · split at h <;> close_throw
          · dsimp only at h
            split at h
            · close_throw
            · obtain ⟨nested, -, h⟩ := exceptBind_ok h
              split at h
              · close_throw
              · split at h
                · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  omega
                · obtain ⟨q, hcop, h⟩ := exceptBind_ok h
                  obtain ⟨stM, gotM⟩ := q
                  split at h
                  · close_throw
                  · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    exact mkCopies_lengths hcop
      · close_throw
    · close_throw
  · close_throw

/-- The walk returned the state it was given. -/
private theorem elimSame {st st' : ElimState} {e e' : Expr}
    (h : (Except.ok (e, st) : CheckM (Expr × ElimState)) = .ok (e', st')) :
    st'.types.length + st.pins.length = st.types.length + st'.pins.length := by
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  omega

/-- **The top-down replace only threads the state**: every state it
returns comes from `replaceIfNested`, so the difference of the two
lengths is an invariant of the whole walk. -/
theorem replaceAllNested_lengths {env : Env} {blvls : List Level} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs₀ st e = .ok (e', st') →
      st'.types.length + st.pins.length = st.types.length + st'.pins.length := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ =>
    intro st st' e' h
    rw [replaceAllNested] at h
    · split at h
      · exact elimSame h
      · split at h
        · close_throw
        · rename_i r heq
          obtain ⟨re, rst⟩ := r
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact replaceIfNested_lengths heq
        · exact elimSame h
    all_goals (intros; exact Expr.noConfusion ‹_›)
  | app f a ihf iha =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_lengths heq
      · split at h
        · close_throw
        · rename_i f' st1 heq1
          split at h
          · close_throw
          · rename_i a' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            have h1 := ihf heq1
            have h2 := iha heq2
            omega
  | lam ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_lengths heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            have h1 := ihty heq1
            have h2 := ihb heq2
            omega
  | forallE ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_lengths heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            have h1 := ihty heq1
            have h2 := ihb heq2
            omega
  | letE ty v b ihty ihv ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_lengths heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i v' st2 heq2
            split at h
            · close_throw
            · rename_i b' st3 heq3
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              have h1 := ihty heq1
              have h2 := ihv heq2
              have h3 := ihb heq3
              omega
  | proj s i x ihx =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_lengths heq
      · split at h
        · close_throw
        · rename_i x' st1 heq1
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ihx heq1

/-- **One type's constructors**: `elimCtors` only threads the state
through `replaceAllNested`. -/
theorem elimCtors_lengths {env : Env} {blvls : List Level} {nP : Nat} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} :
    ∀ {cs : List (Name × Expr × Nat)} {st st' : ElimState}
      {cs' : List (Name × Expr × Nat)},
      elimCtors env blvls nP params pbs₀ cs st = .ok (cs', st') →
      st'.types.length + st.pins.length = st.types.length + st'.pins.length
  | [], st, st', cs', h => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  | (c, cty, nF) :: rest, st, st', cs', h => by
    rw [elimCtors] at h
    split at h
    · split at h
      · obtain ⟨q₁, h₁, h⟩ := exceptBind_ok h
        obtain ⟨cbody', st₁⟩ := q₁
        obtain ⟨q₂, h₂, h⟩ := exceptBind_ok h
        obtain ⟨rest', st₂⟩ := q₂
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have a₁ := replaceAllNested_lengths _ h₁
        have a₂ := elimCtors_lengths h₂
        omega
      · close_throw
    · close_throw

/-- **The worklist**: `elimLoop` sets a type in place — which changes no
length — and otherwise only threads the state through `elimCtors`. -/
theorem elimLoop_lengths {env : Env} {blvls : List Level} {nP : Nat} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} :
    ∀ (fuel qhead : Nat) {st st' : ElimState},
      elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st' →
      st'.types.length + st.pins.length = st.types.length + st'.pins.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro qhead st st' h
    rw [elimLoop] at h
    close_throw
  | succ fuel ih =>
    intro qhead st st' h
    rw [elimLoop] at h
    split at h
    · simp only [Except.ok.injEq] at h
      obtain rfl := h
      omega
    · split at h
      · close_throw
      · rename_i cs' st₁ heq
        have a₁ := elimCtors_lengths heq
        have a₂ := ih (qhead + 1) h
        simp only [List.length_set] at a₂
        omega

/-- **THE ELIMINATION'S COUNT** (task #315): the elimination returns the
types it was given plus exactly one per pin.  Every mint appends one
type and one pin in the same breath, and no other step of the
elimination changes either length. -/
theorem elimNested_types_length {env : Env} {nP : Nat} {lps : List Name}
    {types : List AuxType} {st : ElimState}
    (h : elimNested env nP lps types = .ok st) :
    st.types.length = types.length + st.pins.length := by
  unfold elimNested at h
  split at h
  · split at h
    · split at h
      · have a := elimLoop_lengths _ _ h
        simp only [List.length_nil] at a
        omega
      · close_throw
    · close_throw
  · close_throw

/-! ### The two counts the assembly reads with it -/

/-- The elimination's INPUT is one type per former. -/
theorem nestedTypes0_length (p : NestedParts) (fmsA ctorsA : List ConstantVal) :
    (nestedTypes0 p fmsA ctorsA).length = fmsA.length := by
  simp [nestedTypes0]

/-- The formers' annotation is positional: one checked constant per
declared former. -/
theorem nestedAnnotFormers_length {F : Nat} {env : Env} {nP : Nat} :
    ∀ {formers : List (ConstantVal × Nat)} {fmsA : List ConstantVal},
      nestedAnnotFormers (m := CheckM) (fueledOps mode F) env nP formers = .ok fmsA →
      fmsA.length = formers.length
  | [], fmsA, h => by
    simp only [nestedAnnotFormers, pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    rfl
  | (cv, nIdx) :: rest, fmsA, h => by
    rw [nestedAnnotFormers] at h
    obtain ⟨cvTa₀, -, h⟩ := exceptBind_ok h
    obtain ⟨q, -, h⟩ := exceptBind_ok h
    obtain ⟨cvTa, s⟩ := q
    obtain ⟨restA, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    simp [nestedAnnotFormers_length hrest]

/-- The auxiliary block has one former per type of the elimination. -/
theorem auxBlock_k {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (h : auxBlock p st = some b) : b.k = st.types.length := by
  unfold auxBlock at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨formers, hformers, rfl⟩ := h
  exact mapM_option_length hformers

/-- **THE AUXILIARY BLOCK'S MEMBER COUNT**: the block's own `k` formers
followed by one mimic per pin. -/
theorem auxBlock_k_count {env : Env} {p : NestedParts} {F : Nat}
    {fmsA ctorsA : List ConstantVal} {st : ElimState} {b : MutualBlock}
    (hf : nestedAnnotFormers (m := CheckM) (fueledOps mode F) env p.nP p.formers = .ok fmsA)
    (he : elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA) = .ok st)
    (hb : auxBlock p st = some b) :
    b.k = p.k + st.pins.length := by
  rw [auxBlock_k hb, elimNested_types_length he, nestedTypes0_length,
    nestedAnnotFormers_length hf]
  rfl

/-! ## (C) `mkCopy`, inverted -/

/-- **THE COPY'S COMPONENTS** (task #315 K.28): everything `mkCopy`
stores, read back off a successful call — the level instantiation's
length guard, the former's type, the name, the source record, and the
constructors positionally. -/
theorem mkCopy_inv {pbs : List (Expr × BinderMeta)} {lvls : List Level}
    {Ds : List Expr} {auxName : Name} {J : ContainerMember} {c : AuxType}
    (h : mkCopy pbs lvls Ds auxName J = .ok c) :
    lvls.length = J.lps.length ∧
    (∃ tyI, Expr.instPis (Expr.instantiateLevelParams J.lps lvls J.type) Ds = some tyI ∧
      c.type = closeTelescope pbs 0 tyI) ∧
    c.name = auxName ∧ c.src = some (J.name, lvls, Ds) ∧
    c.ctors.length = J.ctors.length ∧
    ∀ (i : Nat) (cc : ContainerCtor), J.ctors[i]? = some cc →
      ∃ cI, Expr.instPis (Expr.instantiateLevelParams J.lps lvls cc.type) Ds = some cI ∧
        c.ctors[i]? = some (Name.replacePrefix J.name auxName cc.name,
          closeTelescope pbs 0 cI, cc.nFields) := by
  unfold mkCopy at h
  dsimp only at h
  split at h
  · rename_i hlen
    split at h
    · rename_i tyI hty
      obtain ⟨cs, hcs, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl := h
      obtain ⟨hclen, hall⟩ := mapM_except_inv hcs
      refine ⟨by simpa using hlen, ⟨tyI, hty, rfl⟩, rfl, rfl, hclen, ?_⟩
      intro i cc hi
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
      obtain ⟨a, b, ha, hb, hf⟩ := hall i hlt
      obtain rfl : a = cc := Option.some.inj (ha.symm.trans hi)
      split at hf
      · rename_i cI hcI
        simp only [pure, Except.pure, Except.ok.injEq] at hf
        obtain rfl := hf
        exact ⟨cI, hcI, hb⟩
      · close_throw
    · close_throw
  · exfalso
    obtain ⟨r, he, -⟩ := exceptBind_ok h
    exact elimErr_ne_ok he

/-! ## (B) The copy record, inverted -/

/-- **K.28's RECORD, INVERTED** (task #315): `nestedCopySrcOk` is a Bool
over the pin range; this is the package it stands for.  At every pin `q`
the type at `p.k + q` is a MINTED copy — it carries the source the mint
wrote, the pin is that source spelled out, the container is recovered at
the same environment, and `mkCopy` at that source returns the very
former the elimination stored (its name, its type, and its
constructors' names and arities). -/
theorem nestedCopySrcOk_inv {env : Env} {p : NestedParts} {st : ElimState}
    (h : nestedCopySrcOk env p st = true) :
    ∃ (t₀ : AuxType) (pbs : List (Expr × BinderMeta)) (body : Expr),
      st.types.head? = some t₀ ∧ t₀.type.stripPis p.nP = some (pbs, body) ∧
      ∀ (q : Nat) (qn : NestedPin), st.pins[q]? = some qn →
        ∃ (t : AuxType) (Jn : Name) (lvls : List Level) (Ds : List Expr)
          (ci : ContainerInfo) (J : ContainerMember) (c : AuxType),
          st.types[p.k + q]? = some t ∧ t.src = some (Jn, lvls, Ds) ∧ Jn = qn.container ∧
          qn.pin = Expr.mkAppN (.const Jn lvls) Ds ∧ containerInfo? env Jn = some ci ∧
          ci.members.find? (fun J => J.name == Jn) = some J ∧ J.name = Jn ∧
          mkCopy pbs lvls Ds t.name J = .ok c ∧ c.name = t.name ∧ c.type = t.type ∧
          c.ctors.map (fun x => (x.1, x.2.2)) = t.ctors.map (fun x => (x.1, x.2.2)) := by
  unfold nestedCopySrcOk at h
  split at h
  · rename_i pbs body heq
    rw [Option.bind_eq_some_iff] at heq
    obtain ⟨t₀, ht₀, hsp⟩ := heq
    refine ⟨t₀, pbs, body, ht₀, hsp, ?_⟩
    intro q qn hqn
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hqn
    have hq := List.all_eq_true.mp h q (List.mem_range.mpr hlt)
    rw [hqn] at hq
    cases ht : st.types[p.k + q]? with
    | none => simp only [ht] at hq; exact absurd hq (by simp)
    | some t =>
      simp only [ht] at hq
      cases hsrc : t.src with
      | none => simp only [hsrc] at hq; exact absurd hq (by simp)
      | some tr =>
        obtain ⟨Jn, lvls, Ds⟩ := tr
        simp only [hsrc, Bool.and_eq_true, beq_iff_eq] at hq
        obtain ⟨⟨hJn, hpin⟩, hq⟩ := hq
        cases hci : containerInfo? env Jn with
        | none => simp only [hci] at hq; exact absurd hq (by simp)
        | some ci =>
          simp only [hci] at hq
          cases hJ : ci.members.find? (fun J => J.name == Jn) with
          | none => simp only [hJ] at hq; exact absurd hq (by simp)
          | some J =>
            simp only [hJ] at hq
            cases hc : mkCopy pbs lvls Ds t.name J with
            | error e => simp only [hc] at hq; exact absurd hq (by simp)
            | ok c =>
              simp only [hc, Bool.and_eq_true, beq_iff_eq] at hq
              obtain ⟨⟨hcn, hct⟩, hcc⟩ := hq
              have hJname : J.name = Jn := by
                have := List.find?_some hJ
                simpa using this
              exact ⟨t, Jn, lvls, Ds, ci, J, c, rfl, hsrc, hJn, hpin, hci, hJ, hJname,
                hc, hcn, hct, hcc⟩
  · simp at h
