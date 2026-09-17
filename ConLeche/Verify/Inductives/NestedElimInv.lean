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
        -- K.40 threads the worklist position through `ElimState.curType`;
        -- that update changes no length, and `omega` needs it said
        have hT : ({ st with curType := qhead } : ElimState).types.length
            = st.types.length := rfl
        have hP : ({ st with curType := qhead } : ElimState).pins.length
            = st.pins.length := rfl
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

/-! ## (D) The elimination keeps the types it was given

The worklist never drops or reorders a type: `mkCopies` APPENDS the
copies, `replaceIfNested`, `replaceAllNested` and `elimCtors` only
thread the state, and `elimLoop` `set`s the type it is at — with the
same name, the same type and the same source, and with constructors
`elimCtors` renamed nothing in.  So the elimination's list starts with
the list it was given, up to the constructors' types.
-/

/-- An index into a list is an index into any extension of it. -/
private theorem getElem?_of_append {α : Type} {l l' : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : (l ++ l')[i]? = some a := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- **One mint group** only APPENDS: a type the state already carried is
still there, at the same position. -/
theorem mkCopies_types_prefix {env : Env} {pbs : List (Expr × BinderMeta)}
    {lvls : List Level} {Ds : List Expr} {I : Name} {base size : Nat} :
    ∀ {Js : List ContainerMember} {st st' : ElimState} {got : Option Name},
      mkCopies env pbs lvls Ds I base size Js st = .ok (st', got) →
      ∀ (i : Nat) (t : AuxType), st.types[i]? = some t → st'.types[i]? = some t
  | [], st, st', got, h => by
    simp only [mkCopies, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact fun _ _ ht => ht
  | J :: rest, st, st', got, h => by
    rw [mkCopies] at h
    split at h
    obtain ⟨copy, -, h⟩ := exceptBind_ok h
    obtain ⟨q, hrec, h⟩ := exceptBind_ok h
    obtain ⟨stM, gotM⟩ := q
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact fun i t ht => mkCopies_types_prefix hrec i t (getElem?_of_append ht)

/-- **One occurrence**: `replaceIfNested` either passes the state
through or mints, and a mint only appends. -/
theorem replaceIfNested_types_prefix {env : Env} {blvls : List Level} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} {st st' : ElimState} {e e' : Expr}
    (h : replaceIfNested env blvls params pbs₀ st e = .ok (some (e', st'))) :
    ∀ (i : Nat) (t : AuxType), st.types[i]? = some t → st'.types[i]? = some t := by
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
                  exact fun _ _ ht => ht
                · obtain ⟨q, hcop, h⟩ := exceptBind_ok h
                  obtain ⟨stM, gotM⟩ := q
                  split at h
                  · close_throw
                  · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    exact mkCopies_types_prefix hcop
      · close_throw
    · close_throw
  · close_throw

/-- The walk returned the state it was given. -/
private theorem elimSameP {st st' : ElimState} {e e' : Expr}
    (h : (Except.ok (e, st) : CheckM (Expr × ElimState)) = .ok (e', st')) :
    ∀ (i : Nat) (t : AuxType), st.types[i]? = some t → st'.types[i]? = some t := by
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact fun _ _ ht => ht

/-- **The top-down replace only threads the state**, so every type it
was given is still there, at the same position. -/
theorem replaceAllNested_types_prefix {env : Env} {blvls : List Level} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs₀ st e = .ok (e', st') →
      ∀ (i : Nat) (t : AuxType), st.types[i]? = some t → st'.types[i]? = some t := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ =>
    intro st st' e' h
    rw [replaceAllNested] at h
    · split at h
      · exact elimSameP h
      · split at h
        · close_throw
        · rename_i r heq
          obtain ⟨re, rst⟩ := r
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact replaceIfNested_types_prefix heq
        · exact elimSameP h
    all_goals (intros; exact Expr.noConfusion ‹_›)
  | app f a ihf iha =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameP h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_types_prefix heq
      · split at h
        · close_throw
        · rename_i f' st1 heq1
          split at h
          · close_throw
          · rename_i a' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact fun i t ht => iha heq2 i t (ihf heq1 i t ht)
  | lam ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameP h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_types_prefix heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact fun i t ht => ihb heq2 i t (ihty heq1 i t ht)
  | forallE ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameP h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_types_prefix heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact fun i t ht => ihb heq2 i t (ihty heq1 i t ht)
  | letE ty v b ihty ihv ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameP h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_types_prefix heq
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
              exact fun i t ht => ihb heq3 i t (ihv heq2 i t (ihty heq1 i t ht))
  | proj s i x ihx =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameP h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_types_prefix heq
      · split at h
        · close_throw
        · rename_i x' st1 heq1
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ihx heq1

/-- **One type's constructors**: `elimCtors` only threads the state. -/
theorem elimCtors_types_prefix {env : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} :
    ∀ {cs : List (Name × Expr × Nat)} {st st' : ElimState}
      {cs' : List (Name × Expr × Nat)},
      elimCtors env blvls nP params pbs₀ cs st = .ok (cs', st') →
      ∀ (i : Nat) (t : AuxType), st.types[i]? = some t → st'.types[i]? = some t
  | [], st, st', cs', h => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact fun _ _ ht => ht
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
        exact fun i t ht =>
          elimCtors_types_prefix h₂ i t (replaceAllNested_types_prefix _ h₁ i t ht)
      · close_throw
    · close_throw

/-- **THE CONSTRUCTORS' NAMES AND ARITIES ARE UNTOUCHED** (task #315):
`elimCtors` rewrites a constructor's TYPE and nothing else, positionally. -/
theorem elimCtors_names {env : Env} {blvls : List Level} {nP : Nat} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} :
    ∀ {cs : List (Name × Expr × Nat)} {st st' : ElimState}
      {cs' : List (Name × Expr × Nat)},
      elimCtors env blvls nP params pbs₀ cs st = .ok (cs', st') →
      cs'.map (fun c => (c.1, c.2.2)) = cs.map (fun c => (c.1, c.2.2))
  | [], st, st', cs', h => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | (c, cty, nF) :: rest, st, st', cs', h => by
    rw [elimCtors] at h
    split at h
    · split at h
      · obtain ⟨q₁, -, h⟩ := exceptBind_ok h
        obtain ⟨cbody', st₁⟩ := q₁
        obtain ⟨q₂, h₂, h⟩ := exceptBind_ok h
        obtain ⟨rest', st₂⟩ := q₂
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp [elimCtors_names h₂]
      · close_throw
    · close_throw

/-- What the elimination preserves at a type it was given: everything
but the constructors' TYPES. -/
private def AuxSame (t' t : AuxType) : Prop :=
  t'.name = t.name ∧ t'.type = t.type ∧ t'.src = t.src ∧
    t'.ctors.map (fun c => (c.1, c.2.2)) = t.ctors.map (fun c => (c.1, c.2.2))

private theorem AuxSame.refl' (t : AuxType) : AuxSame t t := ⟨rfl, rfl, rfl, rfl⟩

private theorem AuxSame.trans' {a b c : AuxType} (h₁ : AuxSame a b) (h₂ : AuxSame b c) :
    AuxSame a c :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    h₁.2.2.2.trans h₂.2.2.2⟩

/-- The worklist step at `qhead`, as a shape: `elimCtors` renamed
nothing, so the `set` type is the old one with new constructor TYPES. -/
private theorem elimLoop_types_same {env : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} :
    ∀ (fuel qhead : Nat) {st st' : ElimState},
      elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st' →
      ∀ (i : Nat) (t : AuxType), st.types[i]? = some t →
        ∃ t', st'.types[i]? = some t' ∧ AuxSame t' t := by
  intro fuel
  induction fuel with
  | zero =>
    intro qhead st st' h
    rw [elimLoop] at h
    close_throw
  | succ fuel ih =>
    intro qhead st st' h
    rw [elimLoop] at h
    cases htq : st.types[qhead]? with
    | none =>
      simp only [htq, Except.ok.injEq] at h
      obtain rfl := h
      exact fun i t hi => ⟨t, hi, AuxSame.refl' t⟩
    | some tq =>
      simp only [htq] at h
      split at h
      · close_throw
      · rename_i cs' st₁ heq
        intro i t hi
        have h₁ : st₁.types[i]? = some t := elimCtors_types_prefix heq i t hi
        by_cases hiq : i = qhead
        · have hteq : tq = t := by
            rw [hiq] at hi
            exact Option.some.inj (htq.symm.trans hi)
          subst hteq
          have hlt : qhead < st₁.types.length := by
            rw [hiq] at h₁
            exact (List.getElem?_eq_some_iff.mp h₁).1
          have hset : (st₁.types.set qhead { tq with ctors := cs' })[i]?
              = some { tq with ctors := cs' } := by
            rw [hiq]; exact List.getElem?_set_self hlt
          obtain ⟨t', ht', hs⟩ := ih (qhead + 1) h i { tq with ctors := cs' } hset
          exact ⟨t', ht', hs.trans' ⟨rfl, rfl, rfl, elimCtors_names heq⟩⟩
        · have hset : (st₁.types.set qhead { tq with ctors := cs' })[i]? = some t := by
            rw [List.getElem?_set_ne (Ne.symm hiq)]; exact h₁
          exact ih (qhead + 1) h i t hset

/-- **THE ELIMINATION'S WORKLIST KEEPS THE TYPES IT WAS GIVEN**
(task #315): at every position of the state it started from the
elimination's list carries a type with the same name, the same type,
the same source and the same constructor names and field counts — only
the constructors' TYPES are rewritten, and the copies are appended
behind. -/
theorem elimLoop_types_prefix {env : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)}
    {fuel qhead : Nat} {st st' : ElimState}
    (h : elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st') :
    ∀ (i : Nat) (t : AuxType), st.types[i]? = some t →
      ∃ t', st'.types[i]? = some t' ∧ t'.name = t.name ∧ t'.type = t.type ∧
        t'.src = t.src ∧
        t'.ctors.map (fun c => (c.1, c.2.2)) = t.ctors.map (fun c => (c.1, c.2.2)) := by
  intro i t hi
  obtain ⟨t', ht', hn, hty, hsrc, hcs⟩ := elimLoop_types_same _ _ h i t hi
  exact ⟨t', ht', hn, hty, hsrc, hcs⟩

/-- **THE ELIMINATION KEEPS THE BLOCK'S OWN MEMBERS IN PLACE**
(task #315): the elimination's type list starts with the list it was
given, member for member — name, type, source, and the constructors'
names and field counts. -/
theorem elimNested_types_prefix {env : Env} {nP : Nat} {lps : List Name}
    {types : List AuxType} {st : ElimState}
    (h : elimNested env nP lps types = .ok st) :
    ∀ (i : Nat) (t : AuxType), types[i]? = some t →
      ∃ t', st.types[i]? = some t' ∧ t'.name = t.name ∧ t'.type = t.type ∧
        t'.src = t.src ∧
        t'.ctors.map (fun c => (c.1, c.2.2)) = t.ctors.map (fun c => (c.1, c.2.2)) := by
  unfold elimNested at h
  split at h
  · split at h
    · split at h
      · exact elimLoop_types_prefix h
      · close_throw
    · close_throw
  · close_throw

/-! ## (E) The annotation stages are positional and name-preserving -/

/-- **The FORMERS' names survive the front door** (task #315): the
annotated member at position `i` is the declared former at position
`i`, under its own name.  `checkConstantVal` returns its input with the
type replaced, and `checkSumTele` either returns that or runs the door
again on the SAME constant with the reduced telescope. -/
theorem nestedAnnotFormers_names {F : Nat} {env : Env} {nP : Nat} :
    ∀ {formers : List (ConstantVal × Nat)} {fmsA : List ConstantVal},
      nestedAnnotFormers (m := CheckM) (fueledOps mode F) env nP formers = .ok fmsA →
      ∀ (i : Nat) (cvT : ConstantVal), fmsA[i]? = some cvT →
        ∃ cv nIdx, formers[i]? = some (cv, nIdx) ∧ cvT.name = cv.name
  | [], fmsA, h, i, cvT, hi => by
    simp only [nestedAnnotFormers, pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    simp at hi
  | (cv, nIdx) :: rest, fmsA, h, i, cvT, hi => by
    rw [nestedAnnotFormers] at h
    obtain ⟨cvTa₀, hdoor, h⟩ := exceptBind_ok h
    obtain ⟨q, htele, h⟩ := exceptBind_ok h
    obtain ⟨cvTa, s⟩ := q
    obtain ⟨restA, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      obtain rfl := hi
      refine ⟨cv, nIdx, rfl, ?_⟩
      rcases checkSumTele_shape htele with ⟨rfl, -⟩ | ⟨ty, hccv⟩
      · exact (FrontDoorFacts.ofCheck hdoor).name
      · exact (FrontDoorFacts.ofCheck hccv).name
    | succ j =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨cv', nIdx', hf, hn⟩ := nestedAnnotFormers_names hrest j cvT hi
      exact ⟨cv', nIdx', by simpa using hf, hn⟩

/-- **The CONSTRUCTORS' names survive the front door** (task #315): the
annotation is positional and keeps every declared constructor's name. -/
theorem nestedAnnotCtors_names {F : Nat} {envF : Env} :
    ∀ {ctors : List MutualCtor} {ctorsA : List ConstantVal},
      nestedAnnotCtors (m := CheckM) (fueledOps mode F) envF ctors = .ok ctorsA →
      ctorsA.map (·.name) = ctors.map (·.cv.name)
  | [], ctorsA, h => by
    simp only [nestedAnnotCtors, pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    rfl
  | c :: rest, ctorsA, h => by
    rw [nestedAnnotCtors] at h
    obtain ⟨cvCa, hdoor, h⟩ := exceptBind_ok h
    obtain ⟨restA, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨(FrontDoorFacts.ofCheck hdoor).name, nestedAnnotCtors_names hrest⟩

/-- **THE ELIMINATION'S INPUT, POSITIONALLY** (task #315): the type at
position `i` is the annotated former at position `i`, and its
constructors are the annotated constructors the block assigns to member
`i`. -/
theorem nestedTypes0_getElem? {p : NestedParts} {fmsA ctorsA : List ConstantVal}
    {i : Nat} {t : AuxType} (h : (nestedTypes0 p fmsA ctorsA)[i]? = some t) :
    ∃ cvT, fmsA[i]? = some cvT ∧ t.name = cvT.name ∧ t.type = cvT.type ∧
      ∀ c ∈ t.ctors, ∃ mc cvCa, (mc, cvCa) ∈ p.ctors.zip ctorsA ∧
        c.1 = cvCa.name ∧ mc.member = i := by
  unfold nestedTypes0 at h
  rw [List.getElem?_map, List.getElem?_zipIdx] at h
  cases hf : fmsA[i]? with
  | none => rw [hf] at h; simp at h
  | some cvT =>
    rw [hf] at h
    simp only [Nat.zero_add, Option.map_some, Option.some.injEq] at h
    obtain rfl := h
    refine ⟨cvT, rfl, rfl, rfl, ?_⟩
    intro c hc
    obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hc
    obtain ⟨mc, cvCa⟩ := a
    refine ⟨mc, cvCa, ha, ?_, ?_⟩
    · split at hfa
      · simp only [Option.some.injEq] at hfa
        exact (congrArg Prod.fst hfa).symm
      · exact absurd hfa (by simp)
    · split at hfa
      · rename_i hm
        exact beq_iff_eq.mp hm
      · exact absurd hfa (by simp)

/-! ## (F) The auxiliary block's fields -/

/-- **The AUXILIARY BLOCK'S SCALARS AND CONSTRUCTORS** (task #315):
`auxBlock` copies the block's parameter count, level parameters and
eliminator shape, and flattens the elimination's types into the
constructor list, member index by member index. -/
theorem auxBlock_fields {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (h : auxBlock p st = some b) :
    b.nP = p.nP ∧ b.lps = p.lps ∧ b.large = p.large ∧
      b.ctors = (st.types.zipIdx.map fun (t, mIdx) =>
        t.ctors.map fun c => (⟨⟨c.1, p.lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor)).flatten := by
  unfold auxBlock at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨formers, -, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A successful `mapM` in `Option`, positionally. -/
private theorem mapM_option_at {α β : Type} {f : α → Option β} :
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
      obtain ⟨b, hb, hfb⟩ := mapM_option_at hbs k a hi
      exact ⟨b, by simpa using hb, hfb⟩

/-- The auxiliary block's former at a position of the elimination's
type list. -/
private theorem auxBlock_formerAt {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (h : auxBlock p st = some b) :
    ∀ (i : Nat) (t : AuxType), st.types[i]? = some t →
      ∃ nIdx, b.formers[i]? = some ((⟨t.name, p.lps, t.type⟩ : ConstantVal), nIdx) := by
  unfold auxBlock at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨formers, hformers, rfl⟩ := h
  intro i t hi
  obtain ⟨fm, hfm, hft⟩ := mapM_option_at hformers i t hi
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at hft
  obtain ⟨nIdx, -, rfl⟩ := hft
  exact ⟨nIdx, hfm⟩

/-! ## (G) The two composites the model tier reads -/

/-- **THE AUXILIARY BLOCK STARTS WITH THE DECLARED BLOCK** (task #315):
the first `p.k` members of the auxiliary mutual block are the stream's
own members, under their declared names — the annotation is positional
and name-preserving, the elimination keeps its input list in place, and
`auxBlock` reads the names off it. -/
theorem auxBlock_memberNames {env : Env} {p : NestedParts} {F : Nat}
    {fmsA ctorsA : List ConstantVal} {st : ElimState} {b : MutualBlock}
    (hf : nestedAnnotFormers (m := CheckM) (fueledOps mode F) env p.nP p.formers = .ok fmsA)
    (he : elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA) = .ok st)
    (hb : auxBlock p st = some b) :
    b.memberNames.take p.k = p.memberNames := by
  have hlen : fmsA.length = p.k := nestedAnnotFormers_length hf
  refine List.ext_getElem? (fun i => ?_)
  rw [List.getElem?_take]
  split
  · rename_i hlt
    obtain ⟨cvT, hcvT⟩ : ∃ cvT, fmsA[i]? = some cvT :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, (nestedTypes0 p fmsA ctorsA)[i]? = some t₀ :=
      ⟨_, List.getElem?_eq_getElem (by rw [nestedTypes0_length]; omega)⟩
    obtain ⟨cv, nIdx, hfm, hname⟩ := nestedAnnotFormers_names hf i cvT hcvT
    obtain ⟨cvT', hcvT', hn0, -, -⟩ := nestedTypes0_getElem? ht₀
    obtain rfl : cvT' = cvT := Option.some.inj (hcvT'.symm.trans hcvT)
    obtain ⟨t', ht', hn', -, -, -⟩ := elimNested_types_prefix he i t₀ ht₀
    obtain ⟨nIdx', hfo⟩ := auxBlock_formerAt hb i t' ht'
    have hbm : b.memberNames[i]? = some t'.name := by
      simp only [MutualBlock.memberNames, List.getElem?_map, hfo, Option.map_some]
    have hpm : p.memberNames[i]? = some cv.name := by
      simp only [NestedParts.memberNames, List.getElem?_map, hfm, Option.map_some]
    rw [hbm, hpm, hn', hn0, hname]
  · rename_i hge
    have hpl : p.memberNames.length = p.k := by
      simp only [NestedParts.memberNames, List.length_map, NestedParts.k]
    exact (List.getElem?_eq_none (by omega)).symm

/-- **EVERY OWN-MEMBER CONSTRUCTOR OF THE AUXILIARY BLOCK IS A DECLARED
ONE** (task #315): a constructor of the auxiliary block whose member
index is one of the stream's own carries a declared constructor's name —
the elimination rewrites a constructor's TYPE and nothing else, and the
annotation kept the declared names. -/
theorem auxBlock_ctorName_mem {env : Env} {p : NestedParts} {F : Nat}
    {fmsA ctorsA : List ConstantVal} {st : ElimState} {b : MutualBlock}
    (hf : nestedAnnotFormers (m := CheckM) (fueledOps mode F) env p.nP p.formers = .ok fmsA)
    (hc : nestedAnnotCtors (m := CheckM) (fueledOps mode F) (nestedFormerEnv fmsA env)
      p.ctors = .ok ctorsA)
    (he : elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA) = .ok st)
    (hb : auxBlock p st = some b) :
    ∀ (J : Nat) (c : MutualCtor), b.ctors[J]? = some c → c.member < p.k →
      c.cv.name ∈ p.ctors.map (·.cv.name) := by
  have hlen : fmsA.length = p.k := nestedAnnotFormers_length hf
  intro J c hJ hmem
  obtain ⟨-, -, -, hct⟩ := auxBlock_fields hb
  rw [hct] at hJ
  have hcmem := List.mem_of_getElem? hJ
  rw [List.mem_flatten] at hcmem
  obtain ⟨l, hl, hcl⟩ := hcmem
  obtain ⟨tm, htm, rfl⟩ := List.mem_map.mp hl
  obtain ⟨t, mIdx⟩ := tm
  simp only [List.mem_map] at hcl
  obtain ⟨cc, hcc, rfl⟩ := hcl
  have hmIdx : mIdx < p.k := hmem
  have hst : st.types[mIdx]? = some t := List.mk_mem_zipIdx_iff_getElem?.mp htm
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, (nestedTypes0 p fmsA ctorsA)[mIdx]? = some t₀ :=
    ⟨_, List.getElem?_eq_getElem (by rw [nestedTypes0_length]; omega)⟩
  obtain ⟨t', ht', -, -, -, hcs⟩ := elimNested_types_prefix he mIdx t₀ ht₀
  obtain rfl : t' = t := Option.some.inj (ht'.symm.trans hst)
  have hccm : (cc.1, cc.2.2) ∈ t₀.ctors.map (fun x => (x.1, x.2.2)) := by
    rw [← hcs]; exact List.mem_map.mpr ⟨cc, hcc, rfl⟩
  obtain ⟨cc₀, hcc₀, hceq⟩ := List.mem_map.mp hccm
  obtain ⟨cvT, -, -, -, hall⟩ := nestedTypes0_getElem? ht₀
  obtain ⟨mc, cvCa, hz, hn, -⟩ := hall cc₀ hcc₀
  have hname : cc.1 = cvCa.name := (congrArg Prod.fst hceq).symm.trans hn
  have hmemA : cvCa.name ∈ ctorsA.map (·.name) :=
    List.mem_map.mpr ⟨cvCa, (List.of_mem_zip hz).2, rfl⟩
  rw [nestedAnnotCtors_names hc] at hmemA
  show cc.1 ∈ p.ctors.map (·.cv.name)
  rw [hname]
  exact hmemA
