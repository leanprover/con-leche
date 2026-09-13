module

public import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.EnvWF

public section

/-!
# The nested install: the facts the model lane reads (task #279 M-B′)

Shape facts about the nested route's pure and monadic pieces
(`ConLeche/Kernel/Inductives/NestedElim.lean`,
`NestedInstall.lean`), read off their definitions for the model
theorem `declNested` (`ConLeche/Model/Inductives/DeclNested.lean`):

* **the elimination's name ledger** (`elimNested_names`): the auxiliary
  block's type names are the block's own followed by the pins' `aux`
  names in creation order — every copy is minted together with its
  pin (`mkCopies`), and the worklist (`elimLoop`) rewrites a type's
  constructors in place without touching its name;
* **the auxiliary block record** (`auxBlock_inv`): its formers are the
  elimination's types with their index counts, its constructors the
  types' own, its parameter count and level parameters the block's;
* **the read-back** (`auxStoredAll_inv`): one stored record per
  auxiliary member, positionally;
* **the restored recursor types** (`restoreRecTys_inv`): each restored
  type went through `checkConstantVal` under the name the caller
  listed at its position;
* **the freshness of the minted names** (`copiesFresh_inv`), and the
  two cons functions' `find?` at a name they do not carry;
* **the reserved list closes under `.rec`** (`reserved_of_str_rec`):
  a reserved `T.rec` has a reserved `T` — so a copy's recursor name is
  not reserved because its former's name, which `checkMutualCore`
  checked, is not.
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## The elimination's name ledger -/

/-- The elimination's state grows by copies minted together with their
pins: the new pins, and the new types' names are theirs. -/
def ElimGrows (st st' : ElimState) : Prop :=
  ∃ new : List NestedPin, st'.pins = st.pins ++ new ∧
    st'.types.map (·.name) = st.types.map (·.name) ++ new.map (·.aux)

theorem ElimGrows.refl (st : ElimState) : ElimGrows st st :=
  ⟨[], by simp, by simp⟩

theorem ElimGrows.trans {st₁ st₂ st₃ : ElimState}
    (h₁ : ElimGrows st₁ st₂) (h₂ : ElimGrows st₂ st₃) : ElimGrows st₁ st₃ := by
  obtain ⟨n₁, hp₁, ht₁⟩ := h₁
  obtain ⟨n₂, hp₂, ht₂⟩ := h₂
  exact ⟨n₁ ++ n₂, by rw [hp₂, hp₁, List.append_assoc],
    by rw [ht₂, ht₁, List.map_append, List.append_assoc]⟩

/-- A copy carries the name it was minted under. -/
theorem mkCopy_name {pbs : List (Expr × BinderMeta)} {lvls : List Level} {Ds : List Expr}
    {auxName : Name} {J : ContainerMember} {copy : AuxType}
    (h : mkCopy pbs lvls Ds auxName J = .ok copy) : copy.name = auxName := by
  unfold mkCopy at h
  simp only [bind, Except.bind] at h
  repeat' (first | contradiction | split at h)
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl

/-- `mkCopies` mints one type per container member, each with its pin. -/
theorem mkCopies_grows {env : Env} {pbs : List (Expr × BinderMeta)} {lvls : List Level}
    {Ds : List Expr} {I : Name} {base size : Nat} :
    ∀ {members : List ContainerMember} {st st' : ElimState} {got : Option Name},
      mkCopies env pbs lvls Ds I base size members st = .ok (st', got) → ElimGrows st st'
  | [], st, st', got, h => by
    simp only [mkCopies, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ElimGrows.refl st
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
        refine ElimGrows.trans ?_ (mkCopies_grows hq)
        exact ⟨[⟨_, J.name, Expr.mkAppN (.const J.name lvls) Ds, base, size⟩], rfl,
          by simp [mkCopy_name hcopy]⟩

/-- `replaceIfNested` leaves the state alone or mints copies. -/
theorem replaceIfNested_grows {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st : ElimState} {e : Expr}
    {r : Option (Expr × ElimState)}
    (h : replaceIfNested env blvls params pbs st e = .ok r) :
    ∀ e' st', r = some (e', st') → ElimGrows st st' := by
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
           | exact ElimGrows.refl _
           | exact mkCopies_grows (by assumption))

/-- The top-down replace only ever grows the state by copies. -/
theorem replaceAllNested_grows {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} :
    ∀ (e : Expr) {st : ElimState} {r : Expr × ElimState},
      replaceAllNested env blvls params pbs st e = .ok r → ElimGrows st r.2 := by
  intro e
  induction e with
  | bvar i =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ElimGrows.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_grows hr' _ _ rfl
      · obtain rfl := Except.ok.inj h
        exact ElimGrows.refl _
  | fvar idx ty _ =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ElimGrows.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_grows hr' _ _ rfl
      · obtain rfl := Except.ok.inj h
        exact ElimGrows.refl _
  | sort u =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ElimGrows.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_grows hr' _ _ rfl
      · obtain rfl := Except.ok.inj h
        exact ElimGrows.refl _
  | const n us =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ElimGrows.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_grows hr' _ _ rfl
      · obtain rfl := Except.ok.inj h
        exact ElimGrows.refl _
  | lit l =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ElimGrows.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_grows hr' _ _ rfl
      · obtain rfl := Except.ok.inj h
        exact ElimGrows.refl _
  | app f a ihf iha =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ElimGrows.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_grows hr' _ _ rfl
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            show ElimGrows st st₂
            exact (ihf h₁).trans (iha h₂)
  | lam ty b bm ihty ihb =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ElimGrows.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_grows hr' _ _ rfl
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            show ElimGrows st st₂
            exact (ihty h₁).trans (ihb h₂)
  | forallE ty b bm ihty ihb =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ElimGrows.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_grows hr' _ _ rfl
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            show ElimGrows st st₂
            exact (ihty h₁).trans (ihb h₂)
  | letE ty v b ihty ihv ihb =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ElimGrows.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_grows hr' _ _ rfl
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
              show ElimGrows st st₃
              exact ((ihty h₁).trans (ihv h₂)).trans (ihb h₃)
  | proj s i x ihx =>
    intro st r h
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ElimGrows.refl _
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_grows hr' _ _ rfl
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          obtain rfl := Except.ok.inj h
          show ElimGrows st st₁
          exact ihx h₁

/-- One type's constructors rewritten: the state grows by copies. -/
theorem elimCtors_grows {env : Env} {blvls : List Level} {nP : Nat} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} :
    ∀ {cs : List (Name × Expr × Nat)} {st : ElimState}
      {r : List (Name × Expr × Nat) × ElimState},
      elimCtors env blvls nP params pbs₀ cs st = .ok r → ElimGrows st r.2
  | [], st, r, h => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ElimGrows.refl st
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
            have h₁ := replaceAllNested_grows _ hq
            have h₂ := elimCtors_grows hrest
            exact h₁.trans h₂
      · contradiction
    · contradiction

/-- The worklist: every step grows the state by copies and keeps the
names of the types it rewrites. -/
theorem elimLoop_grows {env : Env} {blvls : List Level} {nP : Nat} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} :
    ∀ {fuel qhead : Nat} {st st' : ElimState},
      elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st' → ElimGrows st st'
  | 0, _, _, _, h => nomatch h
  | fuel + 1, qhead, st, st', h => by
    simp only [elimLoop] at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ElimGrows.refl st
    · next t ht =>
      split at h
      · exact nomatch h
      · next cs' st₁ hcs =>
        have h₁ := elimCtors_grows hcs
        have h₂ := elimLoop_grows h
        refine h₁.trans (ElimGrows.trans ?_ h₂)
        -- the `set` keeps the name at `qhead`
        obtain ⟨new, hp, hn⟩ := h₁
        refine ⟨[], by simp, ?_⟩
        simp only [List.map_set, List.map_nil, List.append_nil]
        have hlt : qhead < st₁.types.length := by
          have h1 : qhead < st.types.length := (List.getElem?_eq_some_iff.mp ht).1
          have h2 : st.types.length ≤ st₁.types.length := by
            have := congrArg List.length hn
            simp only [List.length_map, List.length_append] at this
            omega
          omega
        have hget : (st₁.types.map (·.name))[qhead]? = some t.name := by
          rw [hn, List.getElem?_append_left (by simpa using (List.getElem?_eq_some_iff.mp ht).1),
            List.getElem?_map, ht]
          rfl
        refine List.ext_getElem? fun j => ?_
        rw [List.getElem?_set]
        split
        · next hj =>
          subst hj
          rw [if_pos (by simpa using hlt), hget]
        · rfl

/-- **The elimination's name ledger**: the auxiliary block's type names
are the block's own followed by the pins' `aux` names, in creation
order. -/
theorem elimNested_names {env : Env} {nP : Nat} {lps : List Name} {types : List AuxType}
    {st : ElimState} (h : elimNested env nP lps types = .ok st) :
    st.types.map (·.name) = types.map (·.name) ++ st.pins.map (·.aux) := by
  unfold elimNested at h
  repeat' (first | contradiction | split at h)
  all_goals
    obtain ⟨new, hp, hn⟩ := elimLoop_grows h
    simp only [List.nil_append] at hp
    rw [hn, hp]

/-- The auxiliary block has as many types as the block has members
plus pins, and the block's own names lead. -/
theorem elimNested_length {env : Env} {nP : Nat} {lps : List Name} {types : List AuxType}
    {st : ElimState} (h : elimNested env nP lps types = .ok st) :
    st.types.length = types.length + st.pins.length := by
  have := congrArg List.length (elimNested_names h)
  simpa using this

/-- A block member's name, at its position. -/
theorem elimNested_name_lt {env : Env} {nP : Nat} {lps : List Name} {types : List AuxType}
    {st : ElimState} (h : elimNested env nP lps types = .ok st) {t : Nat}
    (ht : t < types.length) :
    st.types[t]?.map (·.name) = types[t]?.map (·.name) := by
  have hn := elimNested_names h
  have := congrArg (fun l => l[t]?) hn
  simp only [List.getElem?_map] at this
  rw [this, List.getElem?_append_left (by simpa using ht), List.getElem?_map]

/-- A copy's name is its pin's `aux`. -/
theorem elimNested_name_copy {env : Env} {nP : Nat} {lps : List Name} {types : List AuxType}
    {st : ElimState} (h : elimNested env nP lps types = .ok st) {j : Nat} :
    st.types[types.length + j]?.map (·.name) = st.pins[j]?.map (·.aux) := by
  have hn := elimNested_names h
  have := congrArg (fun l => l[types.length + j]?) hn
  simp only [List.getElem?_map] at this
  rw [this, List.getElem?_append_right (by simp), List.getElem?_map]
  simp

/-! ## The auxiliary block record -/

/-- A successful `mapM` in `Option`, positionally, with its length. -/
theorem optionMapM_getElem? {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r →
      r.length = l.length ∧
      ∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, r[i]? = some b ∧ f a = some b
  | [], r, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i a ha => by simp at ha⟩
  | a₀ :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b₀, hb₀, bs, hbs, rfl⟩ := h
    obtain ⟨hlen, hall⟩ := optionMapM_getElem? hbs
    refine ⟨by simp [hlen], fun i a ha => ?_⟩
    cases i with
    | zero =>
      obtain rfl := Option.some.inj ha
      exact ⟨b₀, rfl, hb₀⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at ha ⊢
      exact hall i a ha

/-- **The auxiliary block record, read off**: its parameter count,
level parameters and eliminator shape are the block's; its formers are
the elimination's types with their index counts, positionally; its
constructors are the types' own, member by member. -/
theorem auxBlock_inv {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (h : auxBlock p st = some b) :
    b.nP = p.nP ∧ b.lps = p.lps ∧ b.large = p.large ∧ b.elim = p.elim ∧
    b.formers.length = st.types.length ∧
    (∀ (t : Nat) (ty : AuxType), st.types[t]? = some ty →
      ∃ nIdx, auxIdxCount p.nP ty.type = some nIdx ∧
        b.formers[t]? = some (⟨ty.name, p.lps, ty.type⟩, nIdx)) ∧
    b.ctors = (st.types.zipIdx.map fun (t, mIdx) =>
      t.ctors.map fun c => (⟨⟨c.1, p.lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor)).flatten := by
  simp only [auxBlock, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨formers, hmap, rfl⟩ := h
  obtain ⟨hlen, hall⟩ := optionMapM_getElem? hmap
  refine ⟨rfl, rfl, rfl, rfl, hlen, fun t ty hty => ?_, rfl⟩
  obtain ⟨q, hq, hf⟩ := hall t ty hty
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at hf
  obtain ⟨nIdx, hn, rfl⟩ := hf
  exact ⟨nIdx, hn, hq⟩

/-- The auxiliary block's member count is the elimination's type
count. -/
theorem auxBlock_k {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (h : auxBlock p st = some b) : b.k = st.types.length :=
  (auxBlock_inv h).2.2.2.2.1

/-- Member `t`'s recursor name in the auxiliary block is its type's
name under `.rec`. -/
theorem auxBlock_recName {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (h : auxBlock p st = some b) {t : Nat} {ty : AuxType} (hty : st.types[t]? = some ty) :
    b.recName t = ty.name.str "rec" := by
  obtain ⟨-, -, -, -, -, hall, -⟩ := auxBlock_inv h
  obtain ⟨nIdx, -, hf⟩ := hall t ty hty
  unfold MutualBlock.recName
  rw [List.getD_eq_getElem?_getD, hf]
  rfl

/-! ## The read-back -/

/-- One stored record per auxiliary member, positionally. -/
theorem auxStoredAll_inv {envAux : Env} {b : MutualBlock} :
    ∀ {k : Nat} {stored : List AuxStored}, auxStoredAll envAux b k = some stored →
      stored.length = k ∧ ∀ i, i < k → stored[i]? = auxStored? envAux b i
  | 0, stored, h => by
    simp only [auxStoredAll, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => nomatch hi⟩
  | k + 1, stored, h => by
    simp only [auxStoredAll, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨earlier, hearlier, a, ha, rfl⟩ := h
    obtain ⟨hlen, hall⟩ := auxStoredAll_inv hearlier
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    rcases Nat.lt_or_ge i k with hik | hik
    · rw [List.getElem?_append_left (by omega), hall i hik]
    · have : i = k := by omega
      subst this
      rw [List.getElem?_append_right (by omega), ha]
      simp [hlen]

/-- One stored record, read off: the member's former is FOUND at its
name, as an inductive, with the record's checked former. -/
theorem auxStored?_inv {envAux : Env} {b : MutualBlock} {i : Nat} {a : AuxStored}
    (h : auxStored? envAux b i = some a) :
    ∃ (cv : ConstantVal) (nIdx : Nat) (caps : IndCaps),
      b.formers[i]? = some (cv, nIdx) ∧ envAux.find? cv.name = some (.indInfo a.cvTa caps) := by
  unfold auxStored? at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨x, hf, ci, hci, h⟩ := h
  split at h
  · next cvTa caps =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨ci', -, h⟩ := h
    split at h
    · next cvRa mI rP rules =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ctors, -, h⟩ := h
      simp only [pure, Option.some.injEq] at h
      subst h
      exact ⟨x.1, x.2, caps, hf, hci⟩
    · exact nomatch h
  · exact nomatch h

/-! ## The restored recursor types -/

/-- **The restored recursor types, read off**: one per stored record,
each the restored type checked under the name the caller listed at its
position (the record's own where the list is exhausted). -/
theorem restoreRecTys_inv {F : Nat} {env : Env} {R : RestoreTbl} {lps : List Name} :
    ∀ {names : List Name} {l : List AuxStored} {cvs : List ConstantVal},
      restoreRecTys (m := CheckM) (fueledOps mode F) env R lps names l = .ok cvs →
      cvs.length = l.length ∧
      ∀ (i : Nat) (a : AuxStored), l[i]? = some a →
        ∃ (ty : Expr) (cvA : ConstantVal),
          restoreNested R a.cvRa.type = .ok ty ∧
          checkConstantVal (fueledOps mode F) env
            ⟨(names.drop i).headD a.cvRa.name, a.cvRa.levelParams, ty⟩ = .ok cvA ∧
          cvs[i]? = some cvA
  | names, [], cvs, h => by
    simp only [restoreRecTys, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i a ha => by simp at ha⟩
  | names, a :: rest, cvs, h => by
    simp only [restoreRecTys, bind, Except.bind] at h
    obtain ⟨ty, hty, h⟩ := exceptBind_ok h
    obtain ⟨cvA, hcvA, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := restoreRecTys_inv hrest
    refine ⟨by simp [hlen], fun i a' ha' => ?_⟩
    cases i with
    | zero =>
      obtain rfl := Option.some.inj ha'
      exact ⟨ty, cvA, nestedLift_ok hty, by simpa using hcvA, rfl⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at ha' ⊢
      obtain ⟨ty', cvA', h1, h2, h3⟩ := hall i a' ha'
      refine ⟨ty', cvA', h1, ?_, h3⟩
      rw [List.drop_drop] at h2
      simpa [Nat.add_comm] using h2

/-! ## Application spines

The pin is an application spine (`mkAppN (.const J lvls) Ds`), and the
check abstracts and instantiates it and then ANNOTATES it; all three
walks are structural on `.app`, so the spine survives them. -/

/-- Bulk abstraction is structural on a spine. -/
theorem abstractRange_mkAppN (d k c : Nat) :
    ∀ (args : List Expr) (f : Expr),
      (Expr.mkAppN f args).abstractRange d k c
        = Expr.mkAppN (f.abstractRange d k c) (args.map (·.abstractRange d k c))
  | [], _ => rfl
  | a :: args, f => by
    show (Expr.mkAppN (.app f a) args).abstractRange d k c = _
    rw [abstractRange_mkAppN d k c args (.app f a)]
    rfl

/-- Bulk instantiation is structural on a spine. -/
theorem instantiateList_mkAppN (vs : List Expr) (d : Nat) :
    ∀ (args : List Expr) (f : Expr),
      Expr.instantiateList (Expr.mkAppN f args) vs d
        = Expr.mkAppN (Expr.instantiateList f vs d) (args.map (Expr.instantiateList · vs d))
  | [], _ => rfl
  | a :: args, f => by
    show Expr.instantiateList (Expr.mkAppN (.app f a) args) vs d = _
    rw [instantiateList_mkAppN vs d args (.app f a),
      show Expr.instantiateList (.app f a) vs d
        = .app (Expr.instantiateList f vs d) (Expr.instantiateList a vs d) from by
          rw [Expr.instantiateList]]
    rfl

/-- **Annotation keeps a spine a spine**: the head and one argument per
argument, each the annotation of its own (at whatever fuel the walk had
left). -/
theorem annotateCore_mkAppN_inv {env : Env} {d : Nat} :
    ∀ {args : List Expr} {F : Nat} {f e' : Expr},
      annotateCore mode env F d (Expr.mkAppN f args) = .ok e' →
      ∃ (f' : Expr) (args' : List Expr), args'.length = args.length ∧
        e' = Expr.mkAppN f' args' ∧ ∃ F', annotateCore mode env F' d f = .ok f'
  | [], F, f, e', h => ⟨e', [], rfl, rfl, F, h⟩
  | a :: args, F, f, e', h => by
    have h' : annotateCore mode env F d (Expr.mkAppN (.app f a) args) = .ok e' := h
    obtain ⟨g', args', hlen, rfl, F', hg⟩ := annotateCore_mkAppN_inv h'
    cases F' with
    | zero => rw [annotateCore_zero] at hg; exact absurd hg (by simp [throw, throwThe,
        MonadExceptOf.throw])
    | succ F' =>
      obtain ⟨f'', a'', hf, -, rfl⟩ := annotateCore_app_inv hg
      exact ⟨f'', a'' :: args', by simp [hlen], rfl, F', hf⟩

/-- A constant annotates to itself. -/
theorem annotateCore_const_inv {env : Env} {F d : Nat} {n : Name} {us : List Level} {e' : Expr}
    (h : annotateCore mode env F d (.const n us) = .ok e') : e' = .const n us := by
  cases F with
  | zero => rw [annotateCore_zero] at h; exact absurd h (by simp [throw, throwThe,
      MonadExceptOf.throw])
  | succ F =>
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm

/-! ## The replace walk, through a binder

At a `.forallE` node `replaceIfNested` never fires (it answers `none`
on everything but an application), so the walk either PRUNES the node
— and then it prunes both children, since `mentionsConst` is
structural — or descends into the domain and then the body.  Either
way the result is the node with the two children rewritten in that
order, which is the congruence a field's telescope is read through.
-/

/-- The pruned walk is the identity. -/
theorem replaceAllNested_prune {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st : ElimState} {e : Expr}
    (h : st.newNames.any (fun T => e.mentionsConst T) = false) :
    replaceAllNested env blvls params pbs st e = .ok (e, st) := by
  unfold replaceAllNested
  rw [h]
  rfl

/-- **The walk is a congruence at a Π** (and at a λ): the domain first,
then the body, at the state the domain left. -/
theorem replaceAllNested_forallE {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {ty b r : Expr}
    {bm : BinderMeta}
    (h : replaceAllNested env blvls params pbs st (.forallE ty b bm) = .ok (r, st')) :
    ∃ (ty' b' : Expr) (st₁ : ElimState),
      replaceAllNested env blvls params pbs st ty = .ok (ty', st₁) ∧
        replaceAllNested env blvls params pbs st₁ b = .ok (b', st') ∧
        r = .forallE ty' b' bm := by
  rw [replaceAllNested] at h
  split at h
  · next hpr =>
    -- the node is pruned, and so is each child
    simp only [Bool.not_eq_true', List.any_eq_false] at hpr
    have hty : st.newNames.any (fun T => ty.mentionsConst T) = false := by
      rw [List.any_eq_false]
      intro T hT
      have := hpr T hT
      simp only [Expr.mentionsConst, Bool.or_eq_true, not_or, Bool.not_eq_true] at this
      simp [this.1]
    have hb : st.newNames.any (fun T => b.mentionsConst T) = false := by
      rw [List.any_eq_false]
      intro T hT
      have := hpr T hT
      simp only [Expr.mentionsConst, Bool.or_eq_true, not_or, Bool.not_eq_true] at this
      simp [this.2]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ty, b, st, replaceAllNested_prune hty, replaceAllNested_prune hb, rfl⟩
  · -- `replaceIfNested` answers `none` at a non-application
    rw [show replaceIfNested env blvls params pbs st (.forallE ty b bm) = .ok none from rfl] at h
    dsimp only at h
    split at h
    · exact nomatch h
    · next ty' st₁ hty =>
      split at h
      · exact nomatch h
      · next b' st₂ hb =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨ty', b', st₁, hty, hb, rfl⟩

/-- The same congruence at a `λ`. -/
theorem replaceAllNested_lam {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {ty b r : Expr}
    {bm : BinderMeta}
    (h : replaceAllNested env blvls params pbs st (.lam ty b bm) = .ok (r, st')) :
    ∃ (ty' b' : Expr) (st₁ : ElimState),
      replaceAllNested env blvls params pbs st ty = .ok (ty', st₁) ∧
        replaceAllNested env blvls params pbs st₁ b = .ok (b', st') ∧
        r = .lam ty' b' bm := by
  rw [replaceAllNested] at h
  split at h
  · next hpr =>
    simp only [Bool.not_eq_true', List.any_eq_false] at hpr
    have hty : st.newNames.any (fun T => ty.mentionsConst T) = false := by
      rw [List.any_eq_false]
      intro T hT
      have := hpr T hT
      simp only [Expr.mentionsConst, Bool.or_eq_true, not_or, Bool.not_eq_true] at this
      simp [this.1]
    have hb : st.newNames.any (fun T => b.mentionsConst T) = false := by
      rw [List.any_eq_false]
      intro T hT
      have := hpr T hT
      simp only [Expr.mentionsConst, Bool.or_eq_true, not_or, Bool.not_eq_true] at this
      simp [this.2]
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ty, b, st, replaceAllNested_prune hty, replaceAllNested_prune hb, rfl⟩
  · rw [show replaceIfNested env blvls params pbs st (.lam ty b bm) = .ok none from rfl] at h
    dsimp only at h
    split at h
    · exact nomatch h
    · next ty' st₁ hty =>
      split at h
      · exact nomatch h
      · next b' st₂ hb =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨ty', b', st₁, hty, hb, rfl⟩

/-! ## The pins' check -/

/-- **The pins' check, read off** (post-check (a) at either
environment, `pinsOkAux` at the scratch one): every pin's components
are abstracted over the block's parameter range and instantiated at
the opened parameter variables, and the resulting term is ANNOTATED at
the parameter depth and given a type there. -/
theorem nestedPinsOk_inv {F : Nat} {env : Env} {nP : Nat} {fvsA : List Expr} :
    ∀ {pins : List NestedPin},
      nestedPinsOk (m := CheckM) (fueledOps mode F) env nP fvsA pins = .ok () →
      ∀ q ∈ pins, ∃ (e ty : Expr),
        annotateCore mode env F nP
            (Expr.instantiateList (Expr.abstractRange q.pin 0 nP 0) fvsA.reverse) = .ok e ∧
          inferTypeCore mode env F nP e = .ok ty
  | [], _, q, hq => nomatch hq
  | q₀ :: rest, h, q, hq => by
    simp only [nestedPinsOk, bind, Except.bind] at h
    -- the scope guard (K.3): its failure branch is a throw
    split at h
    · obtain ⟨e, he, h⟩ := exceptBind_ok h
      obtain ⟨ty, hty, h⟩ := exceptBind_ok h
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨e, ty, he, hty⟩
      · exact nestedPinsOk_inv h q hq
    · exact nomatch h

/-! ## The minted names, and the conses -/

/-- **The minted names are free**: every copy's type, its recursor and
its constructors find nothing in the pre-block environment. -/
theorem copiesFresh_inv {env : Env} {k : Nat} {st : ElimState}
    (h : copiesFresh env k st = true) :
    ∀ t ∈ st.types.drop k,
      env.find? t.name = none ∧ env.find? (t.name.str "rec") = none ∧
      ∀ c ∈ t.ctors, env.find? c.1 = none := by
  intro t ht
  unfold copiesFresh nestedCopyNames at h
  rw [List.all_eq_true] at h
  have hmem : ∀ n ∈ (t.name :: t.name.str "rec" :: t.ctors.map (·.1)), env.find? n = none := by
    intro n hn
    have := h n (List.mem_flatMap.mpr ⟨t, ht, hn⟩)
    simpa [Option.isNone_iff_eq_none] using this
  refine ⟨hmem _ (by simp), hmem _ (by simp), fun c hc => hmem _ ?_⟩
  simp only [List.mem_cons, List.mem_map]
  exact Or.inr (Or.inr ⟨c, hc, rfl⟩)

/-- A name the formers' conses do not find, the base does not find. -/
theorem consNestedFormers_find?_none :
    ∀ {l : List AuxStored} {env : Env} {n : Name},
      (consNestedFormers l env).find? n = none → env.find? n = none
  | [], _, _, h => h
  | a :: rest, env, n, h => by
    have h' := consNestedFormers_find?_none (l := rest) h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- A name the constructors' conses do not find, the base does not
find. -/
theorem consNestedCtors_find?_none :
    ∀ {l : List (ConstantVal × Nat × Nat)} {env : Env} {n : Name},
      (consNestedCtors l env).find? n = none → env.find? n = none
  | [], _, _, h => h
  | (cv, nP, nF) :: rest, env, n, h => by
    have h' := consNestedCtors_find?_none (l := rest) h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-! ## The reserved list closes under `.rec` -/

/-- A reserved `T.rec` has a reserved `T`: the reserved recursors are
exactly those of the reserved formers. -/
theorem reserved_of_str_rec {T : Name}
    (h : reservedBasisNames.contains (T.str "rec") = true) :
    reservedBasisNames.contains T = true := by
  simp only [reservedBasisNames, eqName, eqReflName, natName, natZeroName, natSuccName,
    punitName, punitUnitName, emptyName, falseName, quotName, quotMkName, quotLiftName,
    quotIndName, quotSoundName, List.contains_cons, List.contains_nil, Bool.or_eq_true,
    beq_iff_eq, Name.str.injEq, String.reduceEq, and_false, false_or, and_true,
    Bool.false_eq_true, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

/-- A name under `.str "rec"` is not a projection function's. -/
theorem isProjFnShape_str_rec (T : Name) : (T.str "rec").isProjFnShape = false := rfl

/-! ## The pins' scope (task #279 K.3 → M.21)

`pinsClosed` records, of every pin ABSTRACTED over the block's
parameters, the pair `ConstWF` demands of a nested rule's stored pins:
no free variable, and the loose bound variables within the parameter
telescope.  Instantiated at the openers of the stored former — `fvar i
ty_i` with `ty_i` scoped at `i` over the earlier openers, as `Opened`
records them — the pin is scoped at `nP`, bvar-closed, and every leaf
it has is an opener: the three facts the reading of the pin consumes
(`pinRead_of`, `Model/Inductives/CopyPins.lean`). -/

/-- `pinsClosed`, per pin. -/
theorem pinsClosed_inv {nP : Nat} {pins : List NestedPin} (h : pinsClosed nP pins = true) :
    ∀ q ∈ pins, (Expr.abstractRange q.pin 0 nP 0).hasFvar = false ∧
      (Expr.abstractRange q.pin 0 nP 0).looseBVarsBounded nP = true := by
  intro q hq
  unfold pinsClosed at h
  rw [List.all_eq_true] at h
  have := h q hq
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this

/-- **A closed term at the openers is scoped**: a term free of free
variables whose loose bound variables lie within `nP` binders,
instantiated at `nP` openers `fvar i ty_i` (each annotated by a term
scoped at `i`, bvar-closed, with leaves among the openers), is scoped
at `nP`, bvar-closed, and has its leaves among the openers.  At
`nP = 0` there are no openers and the term is its own reading. -/
theorem instantiateList_openers_scoped {nP : Nat} {fvs : List Expr} {qa : Expr}
    (hlen : fvs.length = nP) (hfv : qa.hasFvar = false) (hb : qa.looseBVarsBounded nP = true)
    (hvar : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      (∃ ty, x = Expr.fvar i ty) ∧ Expr.WScoped i (Expr.fvarTypeD x) ∧
      (Expr.fvarTypeD x).looseBVarsBounded 0 = true ∧
      ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) :
    Expr.WScoped nP (Expr.instantiateList qa fvs.reverse) ∧
    (Expr.instantiateList qa fvs.reverse).looseBVarsBounded 0 = true ∧
    ∀ l ∈ (Expr.instantiateList qa fvs.reverse).fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
  -- each opener, as a term
  have hmem : ∀ x ∈ fvs, ∃ i ty, x = Expr.fvar i ty ∧ i < nP ∧ Expr.WScoped i ty ∧
      ty.looseBVarsBounded 0 = true ∧ ∀ l ∈ ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    obtain ⟨⟨ty, rfl⟩, hws, hb0, hlv⟩ := hvar i x (by rw [List.getElem?_eq_getElem hi, hxi])
    exact ⟨i, ty, rfl, hlen ▸ hi, hws, hb0, hlv⟩
  have hnil : ∀ l ∈ qa.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
    intro l hl
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv] at hl
    exact nomatch hl
  cases nP with
  | zero =>
    obtain rfl : fvs = [] := List.eq_nil_of_length_eq_zero hlen
    rw [List.reverse_nil, Expr.instantiateList_nil]
    exact ⟨Expr.WScoped.of_not_hasFvar hfv, hb, hnil⟩
  | succ t =>
    rw [← Expr.instSpine_eq_instantiateList fvs t qa hlen]
    refine ⟨instSpine_WScoped t (Expr.WScoped.of_not_hasFvar hfv) fun a ha => ?_, ?_, ?_⟩
    · obtain ⟨i, ty, rfl, hi, hws, -, -⟩ := hmem a ha
      rw [Expr.WScoped]
      exact ⟨hi, hws⟩
    · have h := instSpine_closed (args := fvs) (e := qa)
        (fun a ha => by obtain ⟨i, ty, rfl, -⟩ := hmem a ha; rfl) (by rw [hlen]; exact hb)
      rwa [hlen, Nat.add_sub_cancel] at h
    · intro l hl
      rcases fvarLeaves_instSpine t hl with hl' | ⟨a, ha, hla⟩
      · exact hnil l hl'
      · obtain ⟨i, ty, rfl, -, -, -, hlv⟩ := hmem a ha
        simp only [Expr.fvarLeaves, List.mem_cons] at hla
        rcases hla with rfl | hla
        · exact ha
        · exact hlv l hla

/-! ## Application spines, scoped -/

/-- The arguments of a scoped spine are scoped. -/
theorem WScoped_mkAppN_args {d : Nat} :
    ∀ {args : List Expr} {f : Expr}, Expr.WScoped d (Expr.mkAppN f args) →
      Expr.WScoped d f ∧ ∀ a ∈ args, Expr.WScoped d a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: args, f, h => by
    obtain ⟨hfa, hall⟩ := WScoped_mkAppN_args (args := args) (f := .app f a) h
    rw [Expr.WScoped] at hfa
    exact ⟨hfa.1, fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hfa.2
      · exact hall b hb⟩

/-- The arguments of a bvar-bounded spine are bvar-bounded. -/
theorem looseBVarsBounded_mkAppN_args {k : Nat} :
    ∀ {args : List Expr} {f : Expr}, (Expr.mkAppN f args).looseBVarsBounded k = true →
      f.looseBVarsBounded k = true ∧ ∀ a ∈ args, a.looseBVarsBounded k = true
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: args, f, h => by
    obtain ⟨hfa, hall⟩ := looseBVarsBounded_mkAppN_args (args := args) (f := .app f a) h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hfa
    exact ⟨hfa.1, fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hfa.2
      · exact hall b hb⟩

/-! ## Closing a telescope and opening it again (task #279, session 9)

`closeTelescope bs i body` (`Kernel/Inductives/SumInstall.lean`) rebuilds
a `∀`-telescope from opener-form domains — domain `j` mentions the
openers `fvar (i + j')`, `j' < j` — by abstracting the deeper openers
first; `openPisAtFvars` at depth `i` re-creates exactly those openers.
The round trip is the identity on a body whose leaves at the openers'
indices carry the openers' annotations (`fvarConsistent`) and which is
bvar-closed, and the same of every domain with respect to the earlier
ones — the shape request 4 of DESIGN §M.21 would certify for a copy's
stored types, read back into the OPENED form the model consumes. -/

/-- The openers `closeTelescope`'s telescope re-opens at. -/
def telescopeOpeners : List (Expr × BinderMeta) → Nat → List Expr
  | [], _ => []
  | (dom, _) :: bs, i => Expr.fvar i dom :: telescopeOpeners bs (i + 1)

theorem telescopeOpeners_length :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat), (telescopeOpeners bs i).length = bs.length
  | [], _ => rfl
  | (_, _) :: bs, i => by simp [telescopeOpeners, telescopeOpeners_length bs (i + 1)]

theorem telescopeOpeners_getElem? :
    ∀ (bs : List (Expr × BinderMeta)) (i j : Nat) (b : Expr × BinderMeta), bs[j]? = some b →
      (telescopeOpeners bs i)[j]? = some (Expr.fvar (i + j) b.1)
  | [], _, j, _, h => nomatch h
  | (dom, bm) :: bs, i, 0, b, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rfl
  | (_, _) :: bs, i, j + 1, b, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [telescopeOpeners, List.getElem?_cons_succ]
    rw [telescopeOpeners_getElem? bs (i + 1) j b h, Nat.add_assoc, Nat.add_comm 1 j]

/-- A closed telescope over bvar-closed domains and body is bvar-closed. -/
theorem closeTelescope_looseBVarsBounded :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) (body : Expr),
      (∀ b ∈ bs, b.1.looseBVarsBounded 0 = true) → body.looseBVarsBounded 0 = true →
      (closeTelescope bs i body).looseBVarsBounded 0 = true
  | [], _, _, _, hb => hb
  | (dom, bm) :: bs, i, body, hbs, hb => by
    simp only [closeTelescope, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hbs _ List.mem_cons_self,
      looseBVarsBounded_abstract1 _ 0 (closeTelescope_looseBVarsBounded bs (i + 1) body
        (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb)⟩

/-- Annotation consistency at an index below the telescope's openers
passes through the closing. -/
theorem fvarConsistent_closeTelescope {d : Nat} {ty : Expr} :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) (body : Expr), d < i →
      Expr.fvarConsistent d ty body → (∀ b ∈ bs, Expr.fvarConsistent d ty b.1) →
      Expr.fvarConsistent d ty (closeTelescope bs i body)
  | [], _, _, _, hb, _ => hb
  | (dom, bm) :: bs, i, body, hdi, hb, hbs => by
    simp only [closeTelescope, Expr.fvarConsistent]
    exact ⟨hbs _ List.mem_cons_self,
      fvarConsistent_abstract1 (Nat.ne_of_lt hdi) _ 0
        (fvarConsistent_closeTelescope bs (i + 1) body (Nat.lt_succ_of_lt hdi) hb
          (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')))⟩

/-- **The round trip**: re-opening a closed telescope at its depth
yields its openers and its body. -/
theorem openPisAtFvars_closeTelescope :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) (body : Expr),
      (∀ b ∈ bs, b.1.looseBVarsBounded 0 = true) → body.looseBVarsBounded 0 = true →
      (∀ (j : Nat) (b : Expr × BinderMeta), bs[j]? = some b →
        Expr.fvarConsistent (i + j) b.1 body ∧
        ∀ (j' : Nat) (b' : Expr × BinderMeta), j < j' → bs[j']? = some b' →
          Expr.fvarConsistent (i + j) b.1 b'.1) →
      openPisAtFvars bs.length (closeTelescope bs i body) i = some (telescopeOpeners bs i, body)
  | [], _, _, _, _, _ => rfl
  | (dom, bm) :: bs, i, body, hbs, hb, hcons => by
    have h0 := hcons 0 (dom, bm) rfl
    rw [Nat.add_zero] at h0
    -- the inner telescope is consistently annotated at `i` and bvar-closed
    have hX : Expr.fvarConsistent i dom (closeTelescope bs (i + 1) body) :=
      fvarConsistent_closeTelescope bs (i + 1) body (Nat.lt_succ_self i) h0.1 fun b hb' => by
        obtain ⟨j', hj'⟩ := List.getElem_of_mem hb'
        exact h0.2 (j' + 1) b (Nat.succ_pos j')
          (by rw [List.getElem?_cons_succ, List.getElem?_eq_getElem hj'.1, hj'.2])
    have hbX : (closeTelescope bs (i + 1) body).looseBVarsBounded 0 = true :=
      closeTelescope_looseBVarsBounded bs (i + 1) body
        (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb
    have hrt : ((closeTelescope bs (i + 1) body).abstract1 i 0).instantiate1 (.fvar i dom) 0
        = closeTelescope bs (i + 1) body :=
      abstract1_instantiate1 _ 0 hX hbX
    simp only [List.length_cons, closeTelescope, openPisAtFvars, telescopeOpeners]
    rw [hrt, openPisAtFvars_closeTelescope bs (i + 1) body
      (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb (fun j b hj => ?_)]
    · have h := hcons (j + 1) b (by rw [List.getElem?_cons_succ]; exact hj)
      rw [show i + (j + 1) = i + 1 + j from by omega] at h
      exact ⟨h.1, fun j' b' hlt hj' =>
        h.2 (j' + 1) b' (Nat.succ_lt_succ hlt) (by rw [List.getElem?_cons_succ]; exact hj')⟩

/-! ## The re-mint (K.9): only the copies' TYPES change -/

/-- A type-only rewrite of the list keeps every entry's name and
constructors, and the length. -/
theorem auxTypes_map_type {ts : List AuxType} {f : AuxType → AuxType}
    (hf : ∀ t, (f t).name = t.name ∧ (f t).ctors = t.ctors) :
    (ts.map f).length = ts.length ∧
    ∀ i : Nat, (ts.map f)[i]?.map (fun (t : AuxType) => (t.name, t.ctors))
      = ts[i]?.map (fun (t : AuxType) => (t.name, t.ctors)) := by
  refine ⟨List.length_map .., fun i => ?_⟩
  rw [List.getElem?_map]
  cases ts[i]? with
  | none => rfl
  | some t => simp only [Option.map_some, (hf t).1, (hf t).2]

/-- `remintCopyTypes` keeps names, constructors and the length. -/
theorem remintCopyTypes_inv {F : Nat} {envF env : Env} {nP : Nat} {fvsA : List Expr}
    {pbsA : List (Expr × BinderMeta)} :
    ∀ {pins : List NestedPin} {ts ts' : List AuxType},
      remintCopyTypes (m := CheckM) (fueledOps mode F) envF nP fvsA pbsA env pins ts = .ok ts' →
      ts'.length = ts.length ∧
      ∀ i : Nat, ts'[i]?.map (fun (t : AuxType) => (t.name, t.ctors))
        = ts[i]?.map (fun (t : AuxType) => (t.name, t.ctors))
  | [], ts, ts', h => by
    obtain rfl : ts = ts' := Except.ok.inj h
    exact ⟨rfl, fun _ => rfl⟩
  | q :: qs, ts, ts', h => by
    simp only [remintCopyTypes, bind, Except.bind] at h
    obtain ⟨pinA, -, h⟩ := exceptBind_ok h
    -- the type-only rewrite of the list, in the one arm that rewrites
    have hmap : ∀ (f : AuxType → AuxType), (∀ t, (f t).name = t.name ∧ (f t).ctors = t.ctors) →
        ∀ {ts₂ : List AuxType},
        remintCopyTypes (m := CheckM) (fueledOps mode F) envF nP fvsA pbsA env qs (ts.map f)
          = .ok ts₂ →
        ts₂.length = ts.length ∧
        ∀ i : Nat, ts₂[i]?.map (fun (t : AuxType) => (t.name, t.ctors))
          = ts[i]?.map (fun (t : AuxType) => (t.name, t.ctors)) := by
      intro f hf ts₂ h₂
      have hrest := remintCopyTypes_inv h₂
      have hstep := auxTypes_map_type (ts := ts) hf
      exact ⟨hrest.1.trans hstep.1, fun i => (hrest.2 i).trans (hstep.2 i)⟩
    split at h
    · split at h
      · split at h
        · split at h
          · simp only [pure, Except.pure] at h
            exact hmap _ (fun t => by split <;> exact ⟨rfl, rfl⟩) h
          · simp only [pure, Except.pure] at h
            exact remintCopyTypes_inv h
        · simp only [pure, Except.pure] at h
          exact remintCopyTypes_inv h
      · simp only [pure, Except.pure] at h
        exact remintCopyTypes_inv h
    · simp only [pure, Except.pure] at h
      exact remintCopyTypes_inv h

/-- **The re-mint changes only the copies' types**: the pins, the name
counter, every entry's name and constructors, and the length are the
elimination's. -/
theorem nestedRemint_inv {F : Nat} {env : Env} {p : NestedParts} {st₀ st : ElimState}
    (h : nestedRemint (m := CheckM) (fueledOps mode F) env p st₀ = .ok st) :
    st.pins = st₀.pins ∧ st.nextIdx = st₀.nextIdx ∧
    st.types.length = st₀.types.length ∧
    ∀ i : Nat, st.types[i]?.map (fun (t : AuxType) => (t.name, t.ctors))
      = st₀.types[i]?.map (fun (t : AuxType) => (t.name, t.ctors)) := by
  simp only [nestedRemint, bind, Except.bind] at h
  obtain ⟨cv₀, -, h⟩ := exceptBind_ok h
  obtain ⟨t₀A, -, h⟩ := exceptBind_ok h
  obtain ⟨⟨fvsA₀, r₁⟩, -, h⟩ := exceptBind_ok h
  obtain ⟨⟨pbsA, r₂⟩, -, h⟩ := exceptBind_ok h
  obtain ⟨typesA, hA, h⟩ := exceptBind_ok h
  obtain rfl := (Except.ok.inj h).symm
  obtain ⟨hlen, hi⟩ := remintCopyTypes_inv hA
  exact ⟨rfl, rfl, hlen, hi⟩

/-- The re-mint keeps every entry's name. -/
theorem nestedRemint_name {F : Nat} {env : Env} {p : NestedParts} {st₀ st : ElimState}
    (h : nestedRemint (m := CheckM) (fueledOps mode F) env p st₀ = .ok st) (i : Nat) :
    st.types[i]?.map (·.name) = st₀.types[i]?.map (·.name) := by
  have := (nestedRemint_inv h).2.2.2 i
  generalize st.types[i]? = a at this ⊢
  generalize st₀.types[i]? = b at this ⊢
  cases a <;> cases b <;> simp only [Option.map_some, Option.map_none,
    Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at this ⊢
  exact this.1

/-- The re-mint keeps every entry's constructors. -/
theorem nestedRemint_ctors {F : Nat} {env : Env} {p : NestedParts} {st₀ st : ElimState}
    (h : nestedRemint (m := CheckM) (fueledOps mode F) env p st₀ = .ok st) (i : Nat) :
    st.types[i]?.map (·.ctors) = st₀.types[i]?.map (·.ctors) := by
  have := (nestedRemint_inv h).2.2.2 i
  generalize st.types[i]? = a at this ⊢
  generalize st₀.types[i]? = b at this ⊢
  cases a <;> cases b <;> simp only [Option.map_some, Option.map_none,
    Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at this ⊢
  exact this.2

end ConLeche
