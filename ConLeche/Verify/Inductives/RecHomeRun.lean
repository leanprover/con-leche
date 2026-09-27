module

public import ConLeche.Kernel.Inductives.RecHome
import ConLeche.Verify.ExceptBind

public section

/-!
# The home table, inverted (`Kernel/Inductives/RecHome.lean`)

What a successful run of the home table says, entry by entry
(`homeTable_inv`): a property of entries holds of every entry once it
holds of the member entries (their recomputation in the members'
layout) and of every entry a round adds — a container instance a leaf of
an expanded entry names (`homeLeafNew`), recomputed at the leaf's key.
And what the recursor check's matching says of a matched class
(`homeMatch_some`).
-/

namespace ConLeche

variable {α β ε : Type}

/-- **`mapM` in `Except`, pointwise**: a successful run has one output per
input, each the function's output there. -/
theorem except_mapM_ok {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r →
      r.length = l.length ∧ ∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, r[i]? = some b ∧ f a = .ok b
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun i a h => by simp at h⟩
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; exact nomatch h
    | ok b =>
      rw [hx] at h
      cases hl : l.mapM f with
      | error e => simp only [hl] at h; exact nomatch h
      | ok rs =>
        simp only [hl] at h
        change Except.ok (b :: rs) = Except.ok r at h
        cases h
        obtain ⟨hlen, hall⟩ := except_mapM_ok hl
        refine ⟨by simp [hlen], fun i a hi => ?_⟩
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi; exact ⟨b, rfl, hx⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi ⊢
          exact hall i a hi

/-- An output of a successful `mapM` is the function's output at an input. -/
theorem except_mapM_mem {f : α → Except ε β} {l : List α} {r : List β} (h : l.mapM f = .ok r)
    {b : β} (hb : b ∈ r) : ∃ a ∈ l, f a = .ok b := by
  obtain ⟨hlen, hall⟩ := except_mapM_ok h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  obtain ⟨b', hb', hf⟩ := hall i l[i] (List.getElem?_eq_getElem (by omega))
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hb'
  exact ⟨l[i], List.getElem_mem _, hb' ▸ hf⟩

/-- An input of a successful `mapM` has its output among the outputs. -/
theorem except_mapM_of_mem {f : α → Except ε β} {l : List α} {r : List β}
    (h : l.mapM f = .ok r) {a : α} (ha : a ∈ l) : ∃ b ∈ r, f a = .ok b := by
  obtain ⟨hlen, hall⟩ := except_mapM_ok h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨b, hb, hf⟩ := hall i l[i] (List.getElem?_eq_getElem hi)
  exact ⟨b, List.mem_of_getElem? hb, hf⟩

section Table

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {holes : List Expr}
  {ctorsAs : List (List (ConstantVal × Nat))}

/-- **The member entries, inverted.** -/
theorem homeMembers_inv {T : List HomeEntry}
    (h : homeMembers ops env ctx holes ctorsAs = .ok T) :
    ∀ e ∈ T, ∃ t, t < ctx.names.length ∧
      homeEntryNfs ops env ctx holes (ctx.names.getD t .anonymous) (ctx.lps.map .param)
        (ctorsAs.getD t []) none = .ok e.nfs ∧
      e = { ind := ctx.names.getD t .anonymous, lvls := ctx.lps.map .param, mem := some t,
            key := none, nPc := ctx.nP, ctors := ctorsAs.getD t [], nfs := e.nfs } := by
  intro e he
  unfold homeMembers at h
  obtain ⟨t, ht, hf⟩ := except_mapM_mem h he
  obtain ⟨nfs, hn, hf⟩ := exceptBind_ok hf
  simp only [pure, Except.pure, Except.ok.injEq] at hf
  subst hf
  exact ⟨t, List.mem_range.mp ht, hn, rfl⟩

/-- **A round's additions, inverted**: every entry after the round was
there before, or is an instance of `news` recomputed at its key. -/
theorem homeAdd_cases :
    ∀ {T : List HomeEntry}
      {news : List (Name × List Level × List Expr × Nat × List (ConstantVal × Nat))}
      {T' : List HomeEntry}, homeAdd ops env ctx holes T news = .ok T' →
      ∀ e ∈ T', e ∈ T ∨ ∃ q ∈ news,
        homeEntryNfs ops env ctx holes q.1 q.2.1 q.2.2.2.2 (some q.2.2.1) = .ok e.nfs ∧
        e = { ind := q.1, lvls := q.2.1, mem := none, key := some q.2.2.1, nPc := q.2.2.2.1,
              ctors := q.2.2.2.2, nfs := e.nfs }
  | T, [], T', h => by
    simp only [homeAdd, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact fun e he => Or.inl he
  | T, (I, us, a, nPc, ctors) :: rest, T', h => by
    unfold homeAdd at h
    split at h
    · intro e he
      rcases homeAdd_cases h e he with h1 | ⟨q, hq, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h2⟩
    · obtain ⟨nfs, hn, h⟩ := exceptBind_ok h
      intro e he
      rcases homeAdd_cases h e he with h1 | ⟨q, hq, h2⟩
      · rcases List.mem_append.mp h1 with h1 | h1
        · exact Or.inl h1
        · simp only [List.mem_singleton] at h1
          subst h1
          exact Or.inr ⟨(I, us, a, nPc, ctors), List.mem_cons_self, hn, rfl⟩
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h2⟩

/-- A named instance comes from a leaf of an expanded entry. -/
theorem homeNews_mem {T : List HomeEntry}
    {q : Name × List Level × List Expr × Nat × List (ConstantVal × Nat)}
    (hq : q ∈ homeNews ctx T) :
    ∃ e ∈ T, e.expands = true ∧ ∃ n ∈ e.nfs, ∃ l, some l ∈ n.leaves ∧ homeLeafNew ctx l = some q := by
  simp only [homeNews, List.mem_flatMap] at hq
  obtain ⟨e, he, hq⟩ := hq
  split at hq
  · rename_i hexp
    simp only [List.mem_flatMap, List.mem_filterMap] at hq
    obtain ⟨n, hn, l?, hl, hq⟩ := hq
    cases l? with
    | none => exact nomatch hq
    | some l => exact ⟨e, he, hexp, n, hn, l, hl, hq⟩
  · exact nomatch hq

/-- **The table's invariant** (see the module docstring). -/
theorem homeTable_inv {P : HomeEntry → Prop}
    (h0 : ∀ t nfs, t < ctx.names.length →
      homeEntryNfs ops env ctx holes (ctx.names.getD t .anonymous) (ctx.lps.map .param)
        (ctorsAs.getD t []) none = .ok nfs →
      P { ind := ctx.names.getD t .anonymous, lvls := ctx.lps.map .param, mem := some t,
          key := none, nPc := ctx.nP, ctors := ctorsAs.getD t [], nfs := nfs })
    (hstep : ∀ e, P e → e.expands = true → ∀ n ∈ e.nfs, ∀ l, some l ∈ n.leaves →
      ∀ I us a nPc ctors, homeLeafNew ctx l = some (I, us, a, nPc, ctors) → ∀ nfs,
      homeEntryNfs ops env ctx holes I us ctors (some a) = .ok nfs →
      P { ind := I, lvls := us, mem := none, key := some a, nPc := nPc, ctors := ctors,
          nfs := nfs })
    {m : Nat} {T : List HomeEntry} (h : homeTableAt ops env ctx holes ctorsAs m = .ok T) :
    ∀ e ∈ T, P e := by
  unfold homeTableAt at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h; intro e he; exact nomatch he
  unfold homeTable at h
  obtain ⟨T0, hT0, h⟩ := exceptBind_ok h
  have hP0 : ∀ e ∈ T0, P e := by
    intro e he
    obtain ⟨t, ht, hn, he'⟩ := homeMembers_inv hT0 e he
    rw [he']; exact h0 t e.nfs ht hn
  have iter : ∀ (fuel : Nat) (T T' : List HomeEntry), (∀ e ∈ T, P e) →
      homeIter ops env ctx holes fuel T = .ok T' → ∀ e ∈ T', P e := by
    intro fuel
    induction fuel with
    | zero =>
      intro T T' hT h
      simp only [homeIter, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact hT
    | succ fuel ih =>
      intro T T' hT h
      unfold homeIter at h
      obtain ⟨T1, hT1, h⟩ := exceptBind_ok h
      have hP1 : ∀ e ∈ T1, P e := by
        intro e he
        rcases homeAdd_cases hT1 e he with h1 | ⟨q, hq, hn, he'⟩
        · exact hT e h1
        · obtain ⟨e0, he0, hexp, n, hn0, l, hl, hlq⟩ := homeNews_mem hq
          rw [he']
          obtain ⟨I, us, a, nPc, ctors⟩ := q
          exact hstep e0 (hT e0 he0) hexp n hn0 l hl I us a nPc ctors hlq e.nfs hn
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; exact hP1
      · exact ih T1 T' hP1 h
  exact iter _ T0 T hP0 h

end Table

/-! ## The recursor check's matching -/

/-- The constructor comparison is equality. -/
theorem homeCtorsEq_eq : ∀ {as bs : List (ConstantVal × Nat)}, homeCtorsEq as bs = true → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: as, b :: bs, h => by
    simp only [homeCtorsEq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨⟨n, l, t⟩, k⟩ := a
    obtain ⟨⟨n', l', t'⟩, k'⟩ := b
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rw [homeCtorsEq_eq h5]

/-- **A matched class, inverted**: a member class matched its member's
entry (with the class's constructors), an outside class an entry of its
container at its levels, parameter count and constructors, whose key
reads back to its parameters. -/
theorem homeMatch_some {ctx : NestCtx} {T : List HomeEntry} {C : HomeClass} {r : HomeReach}
    (h : homeMatch ctx T C = some r) :
    ∃ e ∈ T, r.nfs = e.nfs ∧ e.ctors = C.ctors ∧
      ((∃ t, C.member = some t ∧ e.mem = some t ∧ e.key = none ∧ r.key = none) ∨
       (∃ a, C.member = none ∧ e.key = some a ∧ r.key = some a ∧ e.ind = C.ind ∧
          e.lvls = C.lvls ∧ e.nPc = C.nPc ∧ C.ds.map homeErase = a.map (homeRb ctx))) := by
  unfold homeMatch at h
  obtain ⟨e, he, hfe⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨e, he, ?_⟩
  split at hfe
  · rename_i t hmt hk
    split at hfe
    · rename_i hc
      simp only [Option.some.injEq] at hfe
      subst hfe
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨rfl, homeCtorsEq_eq hc.2, Or.inl ⟨t, hmt, hc.1, hk, rfl⟩⟩
    · exact nomatch hfe
  · rename_i a hmt hk
    split at hfe
    · rename_i hc
      simp only [Option.some.injEq] at hfe
      subst hfe
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
      exact ⟨rfl, homeCtorsEq_eq h4, Or.inr ⟨a, hmt, hk, rfl, h1, h2, h3, h5⟩⟩
    · exact nomatch hfe
  · exact nomatch hfe

end ConLeche

namespace ConLeche

/-! ## The readings at a context's names alone -/

section Congr

variable {ctx ctx' : NestCtx} (hn : ctx.names = ctx'.names) (hp : ctx.nP = ctx'.nP)
  (hl : ctx.lps = ctx'.lps)
include hn hp hl

theorem homeRb_congr : homeRb ctx = homeRb ctx' := by
  cases ctx; cases ctx'
  simp only at hn hp hl
  subst hn hp hl
  rfl

theorem homeLeafKey_congr : homeLeafKey ctx = homeLeafKey ctx' := by
  cases ctx; cases ctx'
  simp only at hn hp hl
  subst hn hp hl
  rfl

theorem homeReachable_congr : homeReachable ctx = homeReachable ctx' := by
  cases ctx; cases ctx'
  simp only at hn hp hl
  subst hn hp hl
  rfl

end Congr

/-! ## The recursor check's Boolean checks, read -/

section Checks

variable {ctx : NestCtx} {Cs : List HomeClass} {R : List (Option HomeReach)} {inS : Nat → Bool}

theorem getD_none_lt {α : Type} {l : List (Option α)} {c : Nat} {a : α}
    (h : l.getD c none = some a) : c < l.length := by
  rcases Nat.lt_or_ge c l.length with h' | h'
  · exact h'
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h'] at h; exact nomatch h

/-- **A covered class**: reachable, matched and expanded. -/
theorem homeCovered_true {c : Nat} (h : homeCovered ctx Cs R c = true) :
    homeReachable ctx (Cs.getD c default) = true ∧ ∃ r, R.getD c none = some r ∧ r.expands = true := by
  unfold homeCovered at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  split at h2
  · rename_i r hr; exact ⟨r, hr, h2⟩
  · exact nomatch h2

/-- **The consistency check, read** (at a matched list as long as the
classes). -/
theorem homeConsistent_true (hlen : R.length = Cs.length) (h : homeConsistent ctx Cs R inS = true) :
    ∀ a r, R.getD a none = some r → r.expands = true → ∀ e ∈ r.nfs, ∀ l, some l ∈ e.leaves →
      ∀ c, c < Cs.length → inS c = true → ∀ k,
        homeLeafKey ctx (Cs.getD a default) r.key (Cs.getD c default) l = some k →
        ∃ rc, R.getD c none = some rc ∧ rc.key = k := by
  intro a r hr hexp e he l hl c hc hsc k hk
  unfold homeConsistent at h
  have ha : a < Cs.length := hlen ▸ getD_none_lt hr
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  rw [hr] at h1
  simp only [hexp, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 e he (some l) hl
  simp only [List.all_eq_true, List.mem_range] at h2
  have h3 := h2 c hc
  rw [hsc, hk] at h3
  simp only [Bool.not_true, Bool.false_or] at h3
  split at h3
  · rename_i rc hrc
    exact ⟨rc, hrc, by simpa using h3⟩
  · exact nomatch h3

/-- **The pair check, read.** -/
theorem homePairConsistent_true (h : homePairConsistent Cs R inS = true) :
    ∀ a c, a < Cs.length → c < Cs.length → inS a = true → inS c = true →
      (Cs.getD a default).member = none →
      (Cs.getD a default).ind = (Cs.getD c default).ind →
      (Cs.getD a default).lvls = (Cs.getD c default).lvls →
      (Cs.getD a default).ds.map homeErase = (Cs.getD c default).ds.map homeErase →
      ∀ ra rc, R.getD a none = some ra → R.getD c none = some rc → ra.key = rc.key := by
  intro a c ha hc hsa hsc hmo hi hl hd ra rc hra hrc
  unfold homePairConsistent at h
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h a (List.mem_range.mpr ha)) c
    (List.mem_range.mpr hc)
  rw [hsa, hsc, hmo, hi, hl, hd, hra, hrc] at h1
  simpa using h1

end Checks

end ConLeche
