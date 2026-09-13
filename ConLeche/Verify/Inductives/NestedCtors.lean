module

public import ConLeche.Verify.Inductives.NestedLedger
public import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedLeaves

public section

/-!
# The copies' CONSTRUCTORS, read off the run (task #279 M-B′ step 3l)

`NestedLedger.lean` records every copy's origin — the container member,
the pin, the minted type and the constructors as `elimCtors` rewrote
them — and `NestedInv.lean`'s `nestedCopyCtorType_eq` records what the
scratch install STORES of every constructor of the auxiliary block: the
positivity normalisation of the minted constant, the identity where
the normalisation changes nothing.  This module joins the two at a
copy's constructor:

* **`ctorBase`** — where a type's constructors sit in the auxiliary
  block's one constructor list (`auxBlock` flattens the types'
  constructor lists in order), and **`auxBlock_ctor_getElem?`**: the
  `l`-th constructor of type `t` is entry `ctorBase st t + l`, with
  member `t`;
* **`copyCtor_stored`** — at pin `j`, for every constructor `l` of the
  container member the pin names: the MINTED constructor is the
  container's stored one instantiated at the pin's components and
  closed over the first former's binders (`mkCopy_inv`); the PROCESSED
  one is the minted one re-opened at the block's parameter variables,
  rewritten by `replaceAllNested`, and closed again
  (`elimCtors_getElem?`); and the STORED one is `normCtorValM`'s output
  on the processed constant — the processed constant itself unless the
  positivity normalisation changed it (`nestedCopyCtorType_eq`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## The auxiliary block's constructor layout -/

/-- Where type `t`'s constructors start in the auxiliary block's
constructor list: the earlier types' constructor counts. -/
@[expose] def ctorBase (st : ElimState) (t : Nat) : Nat :=
  ((st.types.take t).map (·.ctors.length)).sum

/-- An element of the flattened, index-tagged constructor lists, at
its type's base. -/
theorem flatten_zipIdx_getElem? {F : AuxType × Nat → List MutualCtor}
    (hF : ∀ x, (F x).length = x.1.ctors.length) :
    ∀ (L : List AuxType) (n t l : Nat) (ty : AuxType) (c : MutualCtor),
      L[t]? = some ty → (F (ty, n + t))[l]? = some c →
      ((L.zipIdx n).map F).flatten[((L.take t).map (·.ctors.length)).sum + l]? = some c
  | [], _, t, _, _, _, h, _ => nomatch h
  | ty' :: L, n, 0, l, ty, c, h, hc => by
    obtain rfl := Option.some.inj h
    simp only [List.zipIdx_cons, List.map_cons, List.flatten_cons, List.take_zero, List.map_nil,
      List.sum_nil, Nat.zero_add]
    rw [Nat.add_zero] at hc
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hc).1]
    exact hc
  | ty' :: L, n, t + 1, l, ty, c, h, hc => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.zipIdx_cons, List.map_cons, List.flatten_cons, List.take_succ_cons,
      List.sum_cons]
    rw [← hF (ty', n), Nat.add_assoc,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    rw [show n + (t + 1) = n + 1 + t by omega] at hc
    exact flatten_zipIdx_getElem? hF L (n + 1) t l ty c h hc

/-- **The `l`-th constructor of type `t` is the auxiliary block's
constructor `ctorBase st t + l`**, tagged with member `t`. -/
theorem auxBlock_ctor_getElem? {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (hb : auxBlock p st = some b) {t : Nat} {ty : AuxType} (hty : st.types[t]? = some ty)
    {l : Nat} {c : Name × Expr × Nat} (hc : ty.ctors[l]? = some c) :
    b.ctors[ctorBase st t + l]? = some ⟨⟨c.1, p.lps, c.2.1⟩, c.2.2, t⟩ := by
  obtain ⟨-, -, -, -, -, -, hctors⟩ := auxBlock_inv hb
  rw [hctors]
  refine flatten_zipIdx_getElem? (fun x => by cases x; simp) st.types 0 t l ty _ hty ?_
  simp only [Nat.zero_add, List.getElem?_map, hc, Option.map_some]

/-! ## The stored constructor of a copy, from the run -/

/-- **What the run says of a copy's constructors** (pin `j`, container
member `J` at levels `lvls` and components `Ds`, the copy `q.aux` =
member `p.k + j` of the auxiliary block): for every constructor `l` of
`J`, the MINTED constructor is `J`'s stored one instantiated at `Ds`
and closed over the first former's binders `pbs`; the PROCESSED one is
the minted one re-opened at the parameter variables `params`, rewritten
by the walk between two states of the elimination, and closed over the
minted one's own binders `pbs'` — the auxiliary block's constructor
`ctorBase st (p.k + j) + l`, of member `p.k + j`; and the constructor
stage STORES `normCtorValM`'s output on the processed constant, which
is that constant itself or that constant with a normalised type
(`nestedCopyCtorType_eq`, K.12/K.13). -/
@[expose] def CopyCtorsStored (mode : CheckMode) (F : Nat) (env : Env) (p : NestedParts) (st : ElimState)
    (b : MutualBlock) (params : List Expr) (pbs : List (Expr × BinderMeta)) (j : Nat)
    (J : ContainerMember) (lvls : List Level) (Ds : List Expr) (q : NestedPin) : Prop :=
  ∃ tyA : AuxType, st.types[p.k + j]? = some tyA ∧ tyA.name = q.aux ∧
    tyA.ctors.length = J.ctors.length ∧
    ∃ (env₁ : Env) (fms : List MutualFormerA) (f₀ : MutualFormerA)
      (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level)),
      mutualFormers (fueledOps mode F) b.nP b.formers env true = .ok (env₁, fms) ∧
      env₁ = consMutualFormers fms env ∧ fms[0]? = some f₀ ∧
      checkMutualCtors (fueledOps mode F) env₁ b fms (Level.isEquiv f₀.s .zero == some true) true
        b.ctors = .ok (ctorsA, sortss) ∧
      ctorsA.length = b.ctors.length ∧
      ∀ (l : Nat) (c : ContainerCtor), J.ctors[l]? = some c →
        ∃ (cI cbody body' : Expr) (pbs' : List (Expr × BinderMeta)) (rest : Expr)
          (sta stb : ElimState) (cA : ConstantVal × Nat),
          Expr.instPis (c.type.instantiateLevelParams J.lps lvls) Ds = some cI ∧
          (closeTelescope pbs 0 cI).stripPis p.nP = some (pbs', rest) ∧
          Expr.instPis (closeTelescope pbs 0 cI) params = some cbody ∧
          replaceAllNested env (p.lps.map Level.param) params pbs sta cbody = .ok (body', stb) ∧
          sta.pins <+: stb.pins ∧ stb.pins <+: st.pins ∧
          tyA.ctors[l]? = some (Name.replacePrefix J.name q.aux c.name,
            closeTelescope pbs' 0 body', c.nFields) ∧
          b.ctors[ctorBase st (p.k + j) + l]?
            = some ⟨⟨Name.replacePrefix J.name q.aux c.name, p.lps, closeTelescope pbs' 0 body'⟩,
                c.nFields, p.k + j⟩ ∧
          ctorsA[ctorBase st (p.k + j) + l]? = some cA ∧
          normCtorValM (m := CheckM) (fueledOps mode F) env₁ b.memberNames b.nP c.nFields
            ⟨Name.replacePrefix J.name q.aux c.name, p.lps, closeTelescope pbs' 0 body'⟩
            ⟨Name.replacePrefix J.name q.aux c.name, p.lps, closeTelescope pbs' 0 body'⟩ true
            = .ok cA.1 ∧
          (cA.1 = ⟨Name.replacePrefix J.name q.aux c.name, p.lps, closeTelescope pbs' 0 body'⟩ ∨
            ∃ ty', cA.1 = { (⟨Name.replacePrefix J.name q.aux c.name, p.lps,
              closeTelescope pbs' 0 body'⟩ : ConstantVal) with type := ty' }) ∧
          cA.1.type.projTablesOk env₁ = true

/-- **Every constructor of a copy, from the mint to the store** — from
the ledger's pieces at pin `j` (`elimNested_copy`: the mint, the type
list's entry, the walk over the minted constructors) and the scratch
install. -/
theorem copyCtorsStored_of {env envAux : Env} {p : NestedParts} {st st₁ st₂ : ElimState}
    {b : MutualBlock} {F : Nat} {params : List Expr} {pbs : List (Expr × BinderMeta)}
    (hpbs : pbs.length = p.nP) {J : ContainerMember} {lvls : List Level} {Ds : List Expr}
    {q : NestedPin} {copy : AuxType} {cs' : List (Name × Expr × Nat)} {j : Nat}
    (hmk : mkCopy pbs lvls Ds q.aux J = .ok copy)
    (hty : st.types[p.k + j]? = some { copy with ctors := cs' })
    (helimC : elimCtors env (p.lps.map Level.param) p.nP params pbs copy.ctors st₁
      = .ok (cs', st₂))
    (hst₂ : st₂.pins <+: st.pins) (hb : auxBlock p st = some b)
    (haux : checkMutualCore (m := CheckM) (fueledOps mode F) env b none true = .ok envAux) :
    CopyCtorsStored mode F env p st b params pbs j J lvls Ds q := by
  obtain ⟨-, -, hlenC, hctorsC⟩ := mkCopy_inv hmk
  obtain ⟨hlenCs, hallCs⟩ := elimCtors_getElem? hpbs helimC
  obtain ⟨-, -, -, -, env₁, fms, f₀, -, ctorsA, sortss, -, -, -, -, -, hformers, hf0, -, -, -,
    hctors, -⟩ := checkMutualCore_inv haux
  obtain ⟨-, henv₁⟩ := mutualFormers_inv hformers
  have hlenA : ctorsA.length = b.ctors.length := (checkMutualCtors_inv hctors).1
  have hall : ∀ (j : Nat) (c : MutualCtor) (cA : ConstantVal × Nat),
      b.ctors[j]? = some c → ctorsA[j]? = some cA →
      normCtorValM (m := CheckM) (fueledOps mode F) env₁ b.memberNames b.nP c.nF
          c.cv c.cv true = .ok cA.1 ∧
        (cA.1 = c.cv ∨ ∃ ty', cA.1 = { c.cv with type := ty' }) ∧
        cA.1.type.projTablesOk env₁ = true := by
    intro j c cA hc hcA
    obtain ⟨-, -, hall⟩ := checkMutualCtors_inv hctors
    obtain ⟨-, _sorts, -, hrun⟩ := hall j c cA hc hcA
    obtain ⟨hnorm, hproj⟩ := checkMutualCtor_true_norm hrun
    obtain ⟨hstores, hkeep⟩ := normCtorValM_true_stores hnorm
    exact ⟨hnorm, hstores, hkeep hproj⟩
  refine ⟨{ copy with ctors := cs' }, hty, show copy.name = q.aux from mkCopy_name hmk,
    by show cs'.length = J.ctors.length; rw [hlenCs, hlenC],
    env₁, fms, f₀, ctorsA, sortss, hformers, henv₁, hf0, hctors, hlenA, ?_⟩
  intro l c hc
  obtain ⟨cI, hcI, hcopyL⟩ := hctorsC l c hc
  obtain ⟨pbs', rest, cbody, body', sta, stb, hstrip', hinst, hwalk, hcs'l, -, hstb⟩ :=
    hallCs l _ _ _ hcopyL
  have hb' := auxBlock_ctor_getElem? hb hty hcs'l
  have hlt : ctorBase st (p.k + j) + l < b.ctors.length := (List.getElem?_eq_some_iff.mp hb').1
  obtain ⟨cA, hcA⟩ : ∃ cA, ctorsA[ctorBase st (p.k + j) + l]? = some cA :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenA]; exact hlt)⟩
  obtain ⟨hnorm, hstores, hproj⟩ := hall _ _ _ hb' hcA
  exact ⟨cI, cbody, body', pbs', rest, sta, stb, cA, hcI, hstrip', hinst, hwalk,
    (replaceAllNested_mint hpbs _ hwalk).pins_prefix, hstb.trans hst₂, hcs'l, hb', hcA,
    hnorm, hstores, hproj⟩

/-- The same, at the ledger's origin of pin `j` (`elimNested_copy`). -/
theorem copyCtorsStored_of_run {env envAux : Env} {p : NestedParts} {types : List AuxType}
    {st : ElimState} {b : MutualBlock} {F : Nat}
    (helim : elimNested env p.nP p.lps types = .ok st) (hk : types.length = p.k)
    (hb : auxBlock p st = some b)
    (haux : checkMutualCore (m := CheckM) (fueledOps mode F) env b none true = .ok envAux)
    {j : Nat} (hj : j < st.pins.length) :
    ∃ (t₀ : AuxType) (params : List Expr) (body : Expr) (pbs : List (Expr × BinderMeta))
      (body₀ : Expr),
      types.head? = some t₀ ∧ openPisAtFvars p.nP t₀.type 0 = some (params, body) ∧
      t₀.type.stripPis p.nP = some (pbs, body₀) ∧ pbs.length = p.nP ∧
      ∃ (I : Name) (ci : ContainerInfo) (i j₀ : Nat) (J : ContainerMember) (lvls : List Level)
        (Ds : List Expr) (q : NestedPin),
        containerInfo? env I = some ci ∧ ci.members[i]? = some J ∧ j = j₀ + i ∧
        st.pins[j]? = some q ∧ q.container = J.name ∧
        q.pin = Expr.mkAppN (.const J.name lvls) Ds ∧ q.grpBase = j₀ ∧
        CopyCtorsStored mode F env p st b params pbs j J lvls Ds q := by
  obtain ⟨t₀, params, body, pbs, body₀, ht₀, hop, hstrip, I, ci, i, j₀, J, lvls, Ds, q, copy, st₁,
    st₂, cs', hci, hJ, hjE, -, hq, hqc, hqp, hqb, -, hmk, -, hpbs, -, hty, helimC, -, hst₂, -⟩ :=
    elimNested_copy helim hj
  rw [hk] at hty
  exact ⟨t₀, params, body, pbs, body₀, ht₀, hop, hstrip, hpbs, I, ci, i, j₀, J, lvls, Ds, q, hci,
    hJ, hjE, hq, hqc, hqp, hqb, copyCtorsStored_of hpbs hmk hty helimC hst₂ hb haux⟩


/-! ## A container member is determined by its name -/

/-- **What `containerInfo?` reads of a member**: its stored former (type
and level parameters), and its constructors as the stored recursor's
rules, each a stored constructor record whose parameter count is the
block's. -/
theorem containerInfo?_member {env : Env} {I : Name} {ci : ContainerInfo}
    (h : containerInfo? env I = some ci) :
    ∀ J ∈ ci.members,
      ∃ (cvC : ConstantVal) (caps : IndCaps) (cvR : ConstantVal) (mIc rPc : Nat)
        (rulesC : List RecRule),
        env.find? J.name = some (.indInfo cvC caps) ∧ J.type = cvC.type ∧
        J.lps = cvC.levelParams ∧
        env.find? (J.name.str "rec") = some (.recInfo cvR mIc rPc rulesC) ∧
        rulesC.mapM (fun r =>
          match env.find? r.ctor with
          | some (.ctorInfo cvc nPc nF) =>
            if nPc == ci.nP then some (⟨r.ctor, cvc.type, nF⟩ : ContainerCtor) else none
          | _ => none) = some J.ctors := by
  unfold containerInfo? at h
  split at h
  · exact nomatch h
  simp only [bindOption_eq_some_iff] at h
  obtain ⟨cT, hfT, h⟩ := h
  split at h
  · next cvT caps =>
    simp only [bindOption_eq_some_iff] at h
    obtain ⟨cR, hfR, h⟩ := h
    split at h
    · next cvR mI rP rules =>
      split at h
      · next hle =>
        simp only [bindOption_eq_some_iff] at h
        obtain ⟨nP, hnP, h⟩ := h
        obtain ⟨p, hstrip, h⟩ := h
        obtain ⟨_, recBody⟩ := p
        simp only at h
        split at h
        · next hnames =>
          simp only [bindOption_eq_some_iff] at h
          obtain ⟨members, hmapM, h⟩ := h
          simp only [Option.some.injEq] at h
          subst h
          intro J hJ
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hJ
          obtain ⟨hlen, hall⟩ := optionMapM_getElem? hmapM
          have hiC : i < (containerMembersGo env nP (rP + 1) 0 recBody).length := by
            rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
          obtain ⟨J', hJ', hf⟩ := hall i _ (List.getElem?_eq_getElem hiC)
          obtain rfl : J = J' := Option.some.inj (hi.symm.trans hJ')
          simp only [bindOption_eq_some_iff] at hf
          obtain ⟨cC, hfC, hf⟩ := hf
          split at hf
          · next cvC capsC =>
            simp only [bindOption_eq_some_iff] at hf
            obtain ⟨cRc, hfRc, hf⟩ := hf
            split at hf
            · next cvRc mIc rPc rulesC =>
              split at hf
              · next hlps =>
                simp only [bindOption_eq_some_iff] at hf
                obtain ⟨ctors, hctors, hf⟩ := hf
                simp only [Option.some.injEq] at hf
                subst hf
                exact ⟨cvC, capsC, cvRc, mIc, rPc, rulesC, hfC, rfl, rfl, hfRc, hctors⟩
              · exact nomatch hf
            · exact nomatch hf
          · exact nomatch hf
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- **Two container members with one name are one member**: everything
`containerInfo?` reads of a member is read off the environment at the
member's name — the parameter count only decides whether the
constructor list is read at all, never what it holds. -/
theorem containerInfo?_member_eq {env : Env} {I I' : Name} {ci ci' : ContainerInfo}
    (h : containerInfo? env I = some ci) (h' : containerInfo? env I' = some ci')
    {J J' : ContainerMember} (hJ : J ∈ ci.members) (hJ' : J' ∈ ci'.members)
    (hn : J.name = J'.name) : J = J' := by
  obtain ⟨cvC, caps, cvR, mIc, rPc, rulesC, hfC, hty, hlps, hfR, hctors⟩ :=
    containerInfo?_member h J hJ
  obtain ⟨cvC', caps', cvR', mIc', rPc', rulesC', hfC', hty', hlps', hfR', hctors'⟩ :=
    containerInfo?_member h' J' hJ'
  rw [hn] at hfC hfR
  obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfC.symm.trans hfC'))
  obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj (hfR.symm.trans hfR'))
  -- the constructor lists agree entry by entry
  obtain ⟨hlen, hall⟩ := optionMapM_getElem? hctors
  obtain ⟨hlen', hall'⟩ := optionMapM_getElem? hctors'
  have hcs : J.ctors = J'.ctors := by
    refine List.ext_getElem? fun l => ?_
    by_cases hl : l < rulesC.length
    · obtain ⟨c, hc, hg⟩ := hall l _ (List.getElem?_eq_getElem hl)
      obtain ⟨c', hc', hg'⟩ := hall' l _ (List.getElem?_eq_getElem hl)
      rw [hc, hc']
      split at hg
      · next cvc nPc nF hfc =>
        rw [hfc] at hg'
        simp only at hg'
        split at hg
        · split at hg'
          · rw [← Option.some.inj hg, ← Option.some.inj hg']
          · exact nomatch hg'
        · exact nomatch hg
      · exact nomatch hg
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  cases J with
  | mk n lps ty cs =>
    cases J' with
    | mk n' lps' ty' cs' =>
      simp only at hn hty hlps hty' hlps' hcs
      subst hn hty hlps hty' hlps' hcs
      rfl


/-! ## Mentions, through instantiation and opening -/

/-- A mention after instantiation is a mention of the term or of the
value. -/
theorem Expr.mentionsConst_instantiate1 {T : Name} (v : Expr) :
    ∀ (e : Expr) (d : Nat), (e.instantiate1 v d).mentionsConst T = true →
      e.mentionsConst T = true ∨ v.mentionsConst T = true
  | .bvar i, d, h => by
    simp only [Expr.instantiate1] at h
    split at h
    · exact Or.inr h
    · split at h <;> simp [Expr.mentionsConst] at h
  | .fvar _ _, _, h => Or.inl h
  | .sort _, _, h => by simp [Expr.instantiate1, Expr.mentionsConst] at h
  | .const _ _, _, h => Or.inl h
  | .lit _, _, h => by simp [Expr.instantiate1, Expr.mentionsConst] at h
  | .app f a, d, h => by
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases mentionsConst_instantiate1 v f d h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases mentionsConst_instantiate1 v a d h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .lam ty b _, d, h => by
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases mentionsConst_instantiate1 v ty d h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases mentionsConst_instantiate1 v b (d + 1) h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .forallE ty b _, d, h => by
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases mentionsConst_instantiate1 v ty d h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases mentionsConst_instantiate1 v b (d + 1) h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .letE ty val b, d, h => by
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h
    · rcases mentionsConst_instantiate1 v ty d h with h' | h'
      · exact Or.inl (Or.inl (Or.inl h'))
      · exact Or.inr h'
    · rcases mentionsConst_instantiate1 v val d h with h' | h'
      · exact Or.inl (Or.inl (Or.inr h'))
      · exact Or.inr h'
    · rcases mentionsConst_instantiate1 v b (d + 1) h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .proj s i e, d, h => by
    simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases mentionsConst_instantiate1 v e d h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

/-- A term whose head is the constant `T` mentions `T`. -/
theorem Expr.mentionsConst_of_getAppFn {T : Name} :
    ∀ (e : Expr) (us : List Level), e.getAppFn = .const T us → e.mentionsConst T = true
  | .app f a, us, h => by
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    exact Or.inl (mentionsConst_of_getAppFn f us h)
  | .const n us', us, h => by
    obtain ⟨rfl, -⟩ := Expr.const.inj h
    simp [Expr.mentionsConst]
  | .bvar _, _, h => nomatch h
  | .fvar _ _, _, h => nomatch h
  | .sort _, _, h => nomatch h
  | .lam _ _ _, _, h => nomatch h
  | .forallE _ _ _, _, h => nomatch h
  | .letE _ _ _, _, h => nomatch h
  | .lit _, _, h => nomatch h
  | .proj _ _ _, _, h => nomatch h

/-- **A mention in an opened telescope is a mention in the closed one**:
in the body, or in an opener's annotation (an instantiated domain). -/
theorem openPisAtFvars_mentionsConst {T : Name} :
    ∀ (k : Nat) (e : Expr) (j : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars k e j = some (fvs, body) →
      (body.mentionsConst T = true ∨ ∃ x ∈ fvs, x.fvarTypeD.mentionsConst T = true) →
      e.mentionsConst T = true
  | 0, e, j, fvs, body, h, hm => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hm with hm | ⟨x, hx, -⟩
    · exact hm
    · exact nomatch hx
  | k + 1, .forallE dom b bm, j, fvs, body, h, hm => by
    simp only [openPisAtFvars] at h
    split at h
    · next fvs' body' hrec =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Expr.mentionsConst, Bool.or_eq_true]
      have key : (b.instantiate1 (.fvar j dom)).mentionsConst T = true →
          dom.mentionsConst T = true ∨ b.mentionsConst T = true := by
        intro hb
        rcases Expr.mentionsConst_instantiate1 _ b 0 hb with h1 | h1
        · exact Or.inr h1
        · exact Or.inl h1
      rcases hm with hm | ⟨x, hx, hxm⟩
      · exact key (openPisAtFvars_mentionsConst k _ (j + 1) hrec (Or.inl hm))
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inl hxm
        · exact key (openPisAtFvars_mentionsConst k _ (j + 1) hrec (Or.inr ⟨x, hx, hxm⟩))
    · exact nomatch h
  | k + 1, .bvar _, _, _, _, h, _ => nomatch h
  | k + 1, .fvar _ _, _, _, _, h, _ => nomatch h
  | k + 1, .sort _, _, _, _, h, _ => nomatch h
  | k + 1, .const _ _, _, _, _, h, _ => nomatch h
  | k + 1, .app _ _, _, _, _, h, _ => nomatch h
  | k + 1, .lam _ _ _, _, _, _, h, _ => nomatch h
  | k + 1, .letE _ _ _, _, _, _, h, _ => nomatch h
  | k + 1, .lit _, _, _, _, h, _ => nomatch h
  | k + 1, .proj _ _ _, _, _, _, h, _ => nomatch h

end ConLeche
