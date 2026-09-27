module

public import ConLeche.Kernel.Inductives.RecNestK
import ConLeche.Verify.ExceptBind

public section

/-!
# The recursor check's nested route, inverted (PRIMREC / NESTKN-RP)

`targetNestRouteK` (`Kernel/Inductives/RecNestK.lean`) is a worklist over PAIRS
(class, instance, layout, member): it seeds the installing block's member classes at
the root, processes every pair's calls — strictly inside a hot component, softly into
another — adds the callees' pairs, seeds the hot classes the block does not reach at an
older home's root, and finally asks every hot class to be paired.  This module turns a
successful run into facts about its FINAL state (`NestRouteRun`):

* the state only grows (`RouteLe`: every array a prefix of the later one), so a fact read
  at the state a pair was processed at holds at the end;
* every home is `homeRK`'s, every layout `rootLayRK`'s or `contLayRK`'s at its home
  (`LaysOk`), every instance a seed class's (`InstsOk`);
* every pair names a valid instance, layout and member of the right inductive, its
  class's constructors agree with the member's, and it is a SEED or the CALLEE of a
  matched call of an earlier pair (`PairOk`);
* every pair's calls were checked (`CallFact`): a call inside a hot component STRICTLY
  (`StrictRun`: the per-component match, the call's typing at the relocated holes, the
  callee's pair at the node the leaf names), a call into another component softly (a
  successful match gives the callee's pair);
* every hot class is paired (`hcover`).

The facts are stated at an arbitrary `ops : CheckerOps CheckM`; the route runs at
`ShadowOps.ofOps ops` (the pure fold's `ShadowOps.fueled`).
-/

namespace ConLeche

/-! ## Small monad facts -/

theorem throwRK_ne_ok {α : Type} {e : CheckError} {a : α} :
    (throw e : CheckM α) ≠ .ok a := by
  simp [throw, throwThe, MonadExceptOf.throw]

theorem unwrapOrRK_ok {α : Type} {x : Option α} {e : CheckError} {a : α}
    (h : (unwrapOr x e : CheckM α) = .ok a) : x = some a := by
  cases x with
  | none => exact absurd h (by simp [unwrapOr, throw, throwThe, MonadExceptOf.throw])
  | some b =>
    simp only [unwrapOr, pure, Except.pure, Except.ok.injEq] at h
    rw [h]

theorem pureRK_ok {α : Type} {a b : α} (h : (pure a : CheckM α) = .ok b) : a = b := by
  simpa [pure, Except.pure] using h

/-! ## The state only grows -/

/-- **A later state**: every array of the route's state a prefix of the later one. -/
structure RouteLe (st st' : RouteRK) : Prop where
  homes : st.homes.toList <+: st'.homes.toList
  homeNames : st.homeNames.toList <+: st'.homeNames.toList
  insts : st.insts.toList <+: st'.insts.toList
  lays : st.lays.toList <+: st'.lays.toList
  pairs : st.pairs.toList <+: st'.pairs.toList
  spells : st.spells.toList <+: st'.spells.toList
  nis : st.nis.toList <+: st'.nis.toList

theorem RouteLe.refl (st : RouteRK) : RouteLe st st :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
    List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩

theorem RouteLe.trans {a b c : RouteRK} (h₁ : RouteLe a b) (h₂ : RouteLe b c) : RouteLe a c :=
  ⟨h₁.homes.trans h₂.homes, h₁.homeNames.trans h₂.homeNames, h₁.insts.trans h₂.insts,
    h₁.lays.trans h₂.lays, h₁.pairs.trans h₂.pairs, h₁.spells.trans h₂.spells,
    h₁.nis.trans h₂.nis⟩

theorem array_getElem?_of_prefix {α : Type} {a b : Array α} (h : a.toList <+: b.toList)
    {i : Nat} {x : α} (hx : a[i]? = some x) : b[i]? = some x := by
  rw [← Array.getElem?_toList] at hx ⊢
  obtain ⟨t, ht⟩ := h
  rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]
  exact hx

theorem array_mem_of_prefix {α : Type} {a b : Array α} (h : a.toList <+: b.toList) {x : α}
    (hx : x ∈ a) : x ∈ b := by
  rw [← Array.mem_toList_iff] at hx ⊢
  exact h.subset hx

theorem array_prefix_push {α : Type} (a : Array α) (x : α) : a.toList <+: (a.push x).toList := by
  rw [Array.toList_push]; exact List.prefix_append _ _

theorem RouteLe.lay {st st' : RouteRK} (h : RouteLe st st') {i : Nat} {l : LayRK}
    (hl : st.lays[i]? = some l) : st'.lays[i]? = some l := array_getElem?_of_prefix h.lays hl

theorem RouteLe.home {st st' : RouteRK} (h : RouteLe st st') {i : Nat} {H : HomeRK}
    (hl : st.homes[i]? = some H) : st'.homes[i]? = some H := array_getElem?_of_prefix h.homes hl

theorem RouteLe.inst {st st' : RouteRK} (h : RouteLe st st') {i : Nat} {I : InstRK}
    (hl : st.insts[i]? = some I) : st'.insts[i]? = some I := array_getElem?_of_prefix h.insts hl

theorem RouteLe.pair {st st' : RouteRK} (h : RouteLe st st') {q : PairRK}
    (hq : q ∈ st.pairs) : q ∈ st'.pairs := array_mem_of_prefix h.pairs hq

theorem RouteLe.pairAt {st st' : RouteRK} (h : RouteLe st st') {k : Nat} {q : PairRK}
    (hq : st.pairs[k]? = some q) : st'.pairs[k]? = some q := array_getElem?_of_prefix h.pairs hq

theorem RouteLe.ni {st st' : RouteRK} (h : RouteLe st st') {i : Nat}
    {x : Nat × List (Nat × Expr)} (hl : st.nis[i]? = some x) : st'.nis[i]? = some x :=
  array_getElem?_of_prefix h.nis hl

theorem RouteLe.spell {st st' : RouteRK} (h : RouteLe st st') {i : Nat}
    {s : Nat × NestKey × List (List (List Expr)) × LayoutK}
    (hl : st.spells[i]? = some s) : st'.spells[i]? = some s :=
  array_getElem?_of_prefix h.spells hl

/-! ## The operations on the state -/

section Ops

variable {ops : CheckerOps CheckM} {env : Env}

/-- **A home, found or read**: the index holds a home with the class's home's names, read
by `homeRK` at some class; nothing else changes. -/
theorem homeIdxRK_ok {fe : FEnv} {p : BlockShape} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {M : TargetMajor} {st st' : RouteRK} {h : Nat}
    (hr : homeIdxRK (m := CheckM) fe p cvTas ctorsAs M st = .ok (h, st')) :
    RouteLe st st' ∧ st'.lays = st.lays ∧ st'.insts = st.insts ∧ st'.pairs = st.pairs ∧
      st'.next = st.next ∧ st'.spells = st.spells ∧
      ∃ H, homeRK (m := CheckM) fe p cvTas ctorsAs M = .ok H ∧
        ((st'.homes = st.homes ∧ st'.homeNames = st.homeNames ∧
            st.homeNames[h]? = some H.ctx.names) ∨
          (st'.homes = st.homes.push H ∧ st'.homeNames = st.homeNames.push H.ctx.names ∧
            h = st.homes.size)) := by
  unfold homeIdxRK at hr
  obtain ⟨H, hH, hr⟩ := exceptBind_ok hr
  split at hr
  · next i hi =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm
    refine ⟨RouteLe.refl _, rfl, rfl, rfl, rfl, rfl, H, hH, Or.inl ⟨rfl, rfl, ?_⟩⟩
    obtain ⟨hlt, hbeq, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    rw [Array.getElem?_eq_getElem hlt]
    simpa using hbeq
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm
    refine ⟨⟨array_prefix_push _ _, array_prefix_push _ _, List.prefix_refl _,
      List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩, rfl, rfl, rfl, rfl, rfl,
      H, hH, Or.inr ⟨rfl, rfl, rfl⟩⟩

theorem homeIdxRK_nis {fe : FEnv} {p : BlockShape} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {M : TargetMajor} {st st' : RouteRK} {h : Nat}
    (hr : homeIdxRK (m := CheckM) fe p cvTas ctorsAs M st = .ok (h, st')) : st'.nis = st.nis := by
  unfold homeIdxRK at hr
  obtain ⟨H, -, hr⟩ := exceptBind_ok hr
  split at hr
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm; rfl
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm; rfl

/-- The lookup `layIdxRK` makes: a layout of home `h`, the root at `none`, a layout of
the key's group at its levels and parameters at `some kc`. -/
@[expose] def layPredRK (h : Nat) (key : Option NestKey) (l : LayRK) : Bool :=
  l.home == h &&
    match l.key, key with
    | none, none => true
    | some k', some kc => k'.lvls == kc.lvls && k'.ds == kc.ds && l.mems.contains kc.cname
    | _, _ => false

/-- **A layout, found or built** (`layIdxRK`): the home exists; the index holds a layout
the lookup accepts, or a new one built at the key (the root, or `contLayRK`). -/
theorem layIdxRK_ok {h : Nat} {key : Option NestKey} {st st' : RouteRK} {i : Nat}
    (hr : layIdxRK ops env h key st = .ok (i, st')) :
    RouteLe st st' ∧ st'.homes = st.homes ∧ st'.insts = st.insts ∧ st'.pairs = st.pairs ∧
      st'.next = st.next ∧ st'.spells = st.spells ∧ st'.homeNames = st.homeNames ∧
      ∃ H l, st.homes[h]? = some H ∧ st'.lays[i]? = some l ∧
        ((st' = st ∧ layPredRK h key l = true) ∨
          (i = st.lays.size ∧ st'.lays = st.lays.push l ∧
            (key = none → rootLayRK ops env h H = .ok l) ∧
            ∀ kc, key = some kc → contLayRK ops env h H kc = .ok l)) := by
  unfold layIdxRK at hr
  obtain ⟨H, hH, hr⟩ := exceptBind_ok hr
  have hH' := unwrapOrRK_ok hH
  have hfind : ∀ j, Array.findIdx? (layPredRK h key) st.lays = some j →
      ∃ l, st.lays[j]? = some l ∧ layPredRK h key l = true := by
    intro j hj
    obtain ⟨hlt, hbeq, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hj
    exact ⟨_, Array.getElem?_eq_getElem hlt, hbeq⟩
  cases key with
  | none =>
    dsimp only at hr
    split at hr
    · next j hj =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm
      obtain ⟨l, hl, hp⟩ := hfind _ hj
      exact ⟨RouteLe.refl _, rfl, rfl, rfl, rfl, rfl, rfl, H, l, hH', hl, Or.inl ⟨rfl, hp⟩⟩
    · obtain ⟨l, hl, hr⟩ := exceptBind_ok hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm
      refine ⟨⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
        array_prefix_push _ _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩, rfl, rfl, rfl, rfl, rfl,
        rfl, H, l, hH', by simp, Or.inr ⟨rfl, rfl, fun _ => hl, fun _ (e : none = some _) => nomatch e⟩⟩
  | some kc =>
    dsimp only at hr
    split at hr
    · next j hj =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm
      obtain ⟨l, hl, hp⟩ := hfind _ hj
      exact ⟨RouteLe.refl _, rfl, rfl, rfl, rfl, rfl, rfl, H, l, hH', hl, Or.inl ⟨rfl, hp⟩⟩
    · obtain ⟨l, hl, hr⟩ := exceptBind_ok hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm
      refine ⟨⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
        array_prefix_push _ _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩, rfl, rfl, rfl, rfl, rfl,
        rfl, H, l, hH', by simp, Or.inr ⟨rfl, rfl, ⟨fun e => by simp at e, fun kc' e => ?_⟩⟩⟩
      obtain rfl := Option.some.inj e
      exact hl

/-- A layout's home and key: the lookup accepted it, or it was built at that key. -/
@[expose] def LayKeyRK (h : Nat) (key : Option NestKey) (l : LayRK) : Prop :=
  layPredRK h key l = true ∨ (l.home = h ∧ l.key = key)

theorem rootLayRK_ok {h : Nat} {H : HomeRK} {l : LayRK}
    (hr : rootLayRK ops env h H = .ok l) : l.home = h ∧ l.key = none := by
  unfold rootLayRK at hr
  obtain ⟨_, _, hr⟩ := exceptBind_ok hr
  obtain ⟨_, _, hr⟩ := exceptBind_ok hr
  obtain rfl := pureRK_ok hr
  exact ⟨rfl, rfl⟩

theorem contLayRK_ok {h : Nat} {H : HomeRK} {kc : NestKey} {l : LayRK}
    (hr : contLayRK ops env h H kc = .ok l) : l.home = h ∧ l.key = some kc := by
  unfold contLayRK at hr
  obtain ⟨_, _, hr⟩ := exceptBind_ok hr
  obtain ⟨_, _, hr⟩ := exceptBind_ok hr
  obtain ⟨_, _, hr⟩ := exceptBind_ok hr
  dsimp only at hr
  split at hr
  · obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain rfl := pureRK_ok hr
    exact ⟨rfl, rfl⟩
  · obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain rfl := pureRK_ok hr
    exact ⟨rfl, rfl⟩

/-- The layout `layIdxRK` returns is at the home and key asked. -/
theorem layIdxRK_key {h : Nat} {key : Option NestKey} {st st' : RouteRK} {i : Nat}
    (hr : layIdxRK ops env h key st = .ok (i, st')) :
    ∃ l, st'.lays[i]? = some l ∧ LayKeyRK h key l := by
  obtain ⟨-, -, -, -, -, -, -, H, l, -, hl, hk⟩ := layIdxRK_ok hr
  refine ⟨l, hl, ?_⟩
  rcases hk with ⟨-, hp⟩ | ⟨-, -, hroot, hcont⟩
  · exact Or.inl hp
  · right
    cases key with
    | none => exact rootLayRK_ok (hroot rfl)
    | some kc => exact contLayRK_ok (hcont kc rfl)

/-- **Only the spellings grow.** -/
@[expose] def SpellsOnly (st st' : RouteRK) : Prop :=
  st'.homes = st.homes ∧ st'.homeNames = st.homeNames ∧ st'.insts = st.insts ∧
    st'.lays = st.lays ∧ st'.pairs = st.pairs ∧ st'.next = st.next ∧
    st.spells.toList <+: st'.spells.toList ∧ st'.nis = st.nis

theorem SpellsOnly.le {st st' : RouteRK} (h : SpellsOnly st st') : RouteLe st st' := by
  obtain ⟨h1, h2, h3, h4, h5, -, h6, h7⟩ := h
  exact ⟨by rw [h1]; exact List.prefix_refl _, by rw [h2]; exact List.prefix_refl _,
    by rw [h3]; exact List.prefix_refl _, by rw [h4]; exact List.prefix_refl _,
    by rw [h5]; exact List.prefix_refl _, h6, by rw [h7]; exact List.prefix_refl _⟩

theorem SpellsOnly.refl (st : RouteRK) : SpellsOnly st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, rfl⟩

theorem spellIdxRK_ok {h : Nat} {K : NestKey} {st st' : RouteRK} {i : Nat}
    (hr : spellIdxRK ops env h K st = .ok (i, st')) : SpellsOnly st st' := by
  unfold spellIdxRK at hr
  split at hr
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm
    exact SpellsOnly.refl _
  · obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, array_prefix_push _ _, rfl⟩

theorem calleeSpellRK_ok {h : Nat} {H : HomeRK} {LS : LayoutK} {q : PairRK} {lay' : LayRK}
    {nf53 : Expr} {st st' : RouteRK} {sp : Nat}
    (hr : calleeSpellRK ops env h H LS q lay' nf53 st = .ok (sp, st')) : SpellsOnly st st' := by
  unfold calleeSpellRK at hr
  dsimp only at hr
  split at hr
  · split at hr
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm; exact SpellsOnly.refl _
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm; exact SpellsOnly.refl _
  · split at hr
    · split at hr
      · obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm; exact SpellsOnly.refl _
      · exact spellIdxRK_ok hr
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm; exact SpellsOnly.refl _
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm; exact SpellsOnly.refl _

/-- **A pair added** (`addPairRK`): already there, or pushed with its class's
constructors agreeing with its member's; only a soft add may add nothing. -/
theorem addPairRK_ok {Ms : List TargetMajor} {strict : Bool} {q : PairRK} {st st' : RouteRK}
    (hr : addPairRK (m := CheckM) Ms strict q st = .ok st') :
    st'.homes = st.homes ∧ st'.homeNames = st.homeNames ∧ st'.insts = st.insts ∧
      st'.lays = st.lays ∧ st'.next = st.next ∧ st'.spells = st.spells ∧
      ((st'.pairs = st.pairs ∧ q ∈ st.pairs) ∨
        (st'.pairs = st.pairs.push q ∧ ∃ lay, st.lays[q.lay]? = some lay ∧
          ctorsAgreeRK (Ms.getD q.cls default).ctors (lay.ctors.getD q.mem []) = true) ∨
        (strict = false ∧ st'.pairs = st.pairs)) := by
  unfold addPairRK at hr
  split at hr
  · next hc =>
    obtain rfl := pureRK_ok hr
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, by simpa using hc⟩⟩
  · obtain ⟨lay, hlay, hr⟩ := exceptBind_ok hr
    have hlay' := unwrapOrRK_ok hlay
    dsimp only at hr
    by_cases hag : ctorsAgreeRK (Ms.getD q.cls default).ctors (lay.ctors.getD q.mem []) = true
    · rw [if_pos hag] at hr
      obtain rfl := pureRK_ok hr
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inl ⟨rfl, lay, hlay', hag⟩)⟩
    · rw [if_neg hag] at hr
      cases strict with
      | true => exact absurd hr throwRK_ne_ok
      | false =>
        obtain rfl := pureRK_ok hr
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

theorem addPairRK_nis {Ms : List TargetMajor} {strict : Bool} {q : PairRK} {st st' : RouteRK}
    (hr : addPairRK (m := CheckM) Ms strict q st = .ok st') : st'.nis = st.nis := by
  unfold addPairRK at hr
  split at hr
  · obtain rfl := pureRK_ok hr; rfl
  · obtain ⟨lay, -, hr⟩ := exceptBind_ok hr
    dsimp only at hr
    split at hr
    · obtain rfl := pureRK_ok hr; rfl
    · split at hr
      · exact absurd hr throwRK_ne_ok
      · obtain rfl := pureRK_ok hr; rfl

theorem addPairRK_le {Ms : List TargetMajor} {strict : Bool} {q : PairRK} {st st' : RouteRK}
    (hr : addPairRK (m := CheckM) Ms strict q st = .ok st') : RouteLe st st' := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ := addPairRK_ok hr
  refine ⟨by rw [h1]; exact List.prefix_refl _, by rw [h2]; exact List.prefix_refl _,
    by rw [h3]; exact List.prefix_refl _, by rw [h4]; exact List.prefix_refl _, ?_,
    by rw [h6]; exact List.prefix_refl _, by rw [addPairRK_nis hr]; exact List.prefix_refl _⟩
  rcases h7 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · rw [h]; exact List.prefix_refl _
  · rw [h]; exact array_prefix_push _ _
  · rw [h]; exact List.prefix_refl _

/-- **Only the layouts grow.** -/
@[expose] def LaysOnly (st st' : RouteRK) : Prop :=
  st'.homes = st.homes ∧ st'.homeNames = st.homeNames ∧ st'.insts = st.insts ∧
    st'.pairs = st.pairs ∧ st'.next = st.next ∧ st'.spells = st.spells ∧
    st.lays.toList <+: st'.lays.toList ∧ st.nis.toList <+: st'.nis.toList

theorem LaysOnly.le {st st' : RouteRK} (h : LaysOnly st st') : RouteLe st st' := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8⟩ := h
  exact ⟨by rw [h1]; exact List.prefix_refl _, by rw [h2]; exact List.prefix_refl _,
    by rw [h3]; exact List.prefix_refl _, h7, by rw [h4]; exact List.prefix_refl _,
    by rw [h6]; exact List.prefix_refl _, h8⟩

theorem LaysOnly.refl (st : RouteRK) : LaysOnly st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, List.prefix_refl _⟩

theorem LaysOnly.trans {a b c : RouteRK} (h₁ : LaysOnly a b) (h₂ : LaysOnly b c) :
    LaysOnly a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := h₂
  exact ⟨by rw [b1, a1], by rw [b2, a2], by rw [b3, a3], by rw [b4, a4], by rw [b5, a5],
    by rw [b6, a6], a7.trans b7, a8.trans b8⟩

theorem layIdxRK_nis {h : Nat} {key : Option NestKey} {st st' : RouteRK} {i : Nat}
    (hr : layIdxRK ops env h key st = .ok (i, st')) : st'.nis = st.nis := by
  obtain ⟨-, -, -, -, -, -, -, H, l, -, -, hk⟩ := layIdxRK_ok hr
  rcases hk with ⟨rfl, -⟩ | -
  · rfl
  · unfold layIdxRK at hr
    obtain ⟨H, -, hr⟩ := exceptBind_ok hr
    cases key <;>
    · dsimp only at hr
      split at hr
      · obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm; rfl
      · obtain ⟨l, -, hr⟩ := exceptBind_ok hr
        obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm; rfl

theorem layIdxRK_laysOnly {h : Nat} {key : Option NestKey} {st st' : RouteRK} {i : Nat}
    (hr : layIdxRK ops env h key st = .ok (i, st')) : LaysOnly st st' := by
  obtain ⟨hle, h1, h2, h3, h4, h5, h6, -⟩ := layIdxRK_ok hr
  exact ⟨h1, h6, h2, h3, h4, h5, hle.lays, by rw [layIdxRK_nis hr]; exact List.prefix_refl _⟩

/-- **A node instance, found or added** (`niIdxRK`). -/
theorem niIdxRK_ok (li : Nat) (σ : List (Nat × Expr)) (st : RouteRK) :
    LaysOnly st (niIdxRK li σ st).2 ∧
      (niIdxRK li σ st).2.nis[(niIdxRK li σ st).1]? = some (li, σ) ∧
      (niIdxRK li σ st).2.lays = st.lays := by
  unfold niIdxRK
  split
  · next i hi =>
    obtain ⟨hlt, hbeq, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
    refine ⟨LaysOnly.refl _, ?_, rfl⟩
    rw [Array.getElem?_eq_getElem hlt]
    simpa using hbeq
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, array_prefix_push _ _⟩, by simp, rfl⟩

/-- An output of a successful `mapM` is the function's output at an input. -/
theorem exceptMapM_memRK {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → ∀ {b : β}, b ∈ r → ∃ a ∈ l, f a = .ok b
  | [], r, h, b, hb => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact nomatch hb
  | x :: l, r, h, b, hb => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; exact nomatch h
    | ok b0 =>
      rw [hx] at h
      cases hl : l.mapM f with
      | error e => simp only [hl] at h; exact nomatch h
      | ok rs =>
        simp only [hl] at h
        change Except.ok (b0 :: rs) = Except.ok r at h
        cases h
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨a, ha, hf⟩ := exceptMapM_memRK hl hb
          exact ⟨a, List.mem_cons_of_mem _ ha, hf⟩

theorem childCtxRK_entries_go {ctx : NestCtx} {L0 : LayoutK} {ni0 : Nat}
    {σ0 : List (Nat × Expr)} {θ : Nat → Option Expr} {l : List Nat} {σ : List (Nat × Expr)}
    (h : l.mapM (fun j => do
      let b ← unwrapOr (θ (ctx.hiAt 0 + j)) (CheckError.internal "nested route: a family unbound at a use")
      match b with
      | Expr.fvar i _ =>
        if (decide (ctx.hiAt 0 ≤ i) && decide (i < ctx.hiAt 0 + L0.nF)) = true then
          unwrapOr σ0[i - ctx.hiAt 0]? (CheckError.internal "nested route: a user family without an entry")
        else pure (ni0, b)
      | _ => pure (ni0, b) : Nat → CheckM (Nat × Expr)) = .ok σ) :
    ∀ e ∈ σ, e.1 = ni0 ∨ e ∈ σ0 := by
  intro e he
  obtain ⟨j, -, hj⟩ := exceptMapM_memRK h he
  obtain ⟨b, -, hj⟩ := exceptBind_ok hj
  split at hj
  · split at hj
    · exact Or.inr (List.mem_of_getElem? (unwrapOrRK_ok hj))
    · exact Or.inl (by rw [← pureRK_ok hj])
  · exact Or.inl (by rw [← pureRK_ok hj])

/-- **A use's bindings name the user's node instance or one of its entries**
(`childCtxRK`). -/
theorem childCtxRK_entries {ctx : NestCtx} {L0 : LayoutK} {ni0 : Nat} {σ0 : List (Nat × Expr)}
    {lay' : LayRK} {ps : List Expr} {σ : List (Nat × Expr)}
    (h : childCtxRK (m := CheckM) ctx L0 ni0 σ0 lay' ps = .ok σ) :
    ∀ e ∈ σ, e.1 = ni0 ∨ e ∈ σ0 := by
  unfold childCtxRK at h
  dsimp only at h
  split at h
  · obtain ⟨_, hp, h⟩ := exceptBind_ok h
    obtain rfl := pureRK_ok hp
    split at h
    · obtain ⟨_, hp, h⟩ := exceptBind_ok h
      obtain rfl := pureRK_ok hp
      exact childCtxRK_entries_go h
    · obtain ⟨_, h, _⟩ := exceptBind_ok h; exact absurd h throwRK_ne_ok
  · obtain ⟨_, h, _⟩ := exceptBind_ok h; exact absurd h throwRK_ne_ok

/-- **The node instances' invariant**: each names an existing layout, and its entries name
node instances of layouts at the same home. -/
@[expose] def NisOkRK (st : RouteRK) : Prop :=
  ∀ (ni li : Nat) σ, st.nis[ni]? = some (li, σ) → ∃ l, st.lays[li]? = some l ∧
    ∀ e ∈ σ, e.1 < ni ∧ ∃ lu σu lu', st.nis[e.1]? = some (lu, σu) ∧ st.lays[lu]? = some lu' ∧
      lu'.home = l.home

theorem NisOkRK.of_eq {st st' : RouteRK} (h : NisOkRK st)
    (hl : st.lays.toList <+: st'.lays.toList) (hnis : st'.nis = st.nis) : NisOkRK st' := by
  intro ni li σ hn
  rw [hnis] at hn
  obtain ⟨l, hl', he⟩ := h ni li σ hn
  refine ⟨l, array_getElem?_of_prefix hl hl', fun e he' => ?_⟩
  obtain ⟨h0, lu, σu, lu', h1, h2, h3⟩ := he e he'
  exact ⟨h0, lu, σu, lu', by rw [hnis]; exact h1, array_getElem?_of_prefix hl h2, h3⟩

theorem NisOkRK.of_laysOnly {st st' : RouteRK} (h : NisOkRK st) (hlo : LaysOnly st st')
    (hnis : st'.nis = st.nis) : NisOkRK st' := by
  intro ni li σ hn
  rw [hnis] at hn
  obtain ⟨l, hl, he⟩ := h ni li σ hn
  refine ⟨l, hlo.le.lay hl, fun e he' => ?_⟩
  obtain ⟨h0, lu, σu, lu', h1, h2, h3⟩ := he e he'
  exact ⟨h0, lu, σu, lu', by rw [hnis]; exact h1, hlo.le.lay h2, h3⟩

/-- A new node instance keeps the invariant when its layout exists and its entries are of
its home. -/
theorem niIdxRK_nisOk {li : Nat} {σ : List (Nat × Expr)} {st : RouteRK} (h : NisOkRK st)
    {l : LayRK} (hl : st.lays[li]? = some l)
    (he : ∀ e ∈ σ, ∃ lu σu lu', st.nis[e.1]? = some (lu, σu) ∧ st.lays[lu]? = some lu' ∧
      lu'.home = l.home) : NisOkRK (niIdxRK li σ st).2 := by
  unfold niIdxRK
  split
  · exact h
  · intro ni li' σ' hn'
    simp only at hn' ⊢
    rcases Nat.lt_or_ge ni st.nis.size with hlt | hge
    · rw [Array.getElem?_push_lt hlt] at hn'
      obtain ⟨l', hl', he'⟩ := h ni li' σ' (by rw [Array.getElem?_eq_getElem hlt]; exact hn')
      refine ⟨l', hl', fun e hee => ?_⟩
      obtain ⟨h0, lu, σu, lu', h1, h2, h3⟩ := he' e hee
      exact ⟨h0, lu, σu, lu', by
        rw [Array.getElem?_push_lt (Array.getElem?_eq_some_iff.mp h1).1,
          ← Array.getElem?_eq_getElem]; exact h1, h2, h3⟩
    · have : ni = st.nis.size := by
        rcases Nat.lt_or_ge ni (st.nis.size + 1) with h1 | h1
        · omega
        · rw [Array.getElem?_eq_none (by simp; omega)] at hn'; exact absurd hn' (by simp)
      subst this
      rw [Array.getElem?_push_size] at hn'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn')
      refine ⟨l, hl, fun e hee => ?_⟩
      obtain ⟨lu, σu, lu', h1, h2, h3⟩ := he e hee
      exact ⟨(Array.getElem?_eq_some_iff.mp h1).1, lu, σu, lu', by
        rw [Array.getElem?_push_lt (Array.getElem?_eq_some_iff.mp h1).1,
          ← Array.getElem?_eq_getElem]; exact h1, h2, h3⟩

/-- **A key's node instance at a use** (`keyNiRK`'s facts): the key's layout, found or
built at the key, and the node instance of that layout with the use's bindings. -/
@[expose] def KeyNiRK (st : RouteRK) (h : Nat) (H : HomeRK) (L0 : LayoutK) (ni0 : Nat)
    (σ0 : List (Nat × Expr)) (kc : NestKey) (ps : List Expr) (li ni : Nat) : Prop :=
  ∃ lay' σ, st.lays[li]? = some lay' ∧ LayKeyRK h (some kc) lay' ∧
    childCtxRK (m := CheckM) H.ctx L0 ni0 σ0 lay' ps = .ok σ ∧ st.nis[ni]? = some (li, σ)

theorem KeyNiRK.mono {st st' : RouteRK} (hle : RouteLe st st') {h : Nat} {H : HomeRK}
    {L0 : LayoutK} {ni0 : Nat} {σ0 : List (Nat × Expr)} {kc : NestKey} {ps : List Expr}
    {li ni : Nat} (hk : KeyNiRK st h H L0 ni0 σ0 kc ps li ni) :
    KeyNiRK st' h H L0 ni0 σ0 kc ps li ni := by
  obtain ⟨lay', σ, h1, h2, h3, h4⟩ := hk
  exact ⟨lay', σ, hle.lay h1, h2, h3, hle.ni h4⟩

theorem keyNiRK_ok {h : Nat} {H : HomeRK} {L0 : LayoutK} {ni0 : Nat} {σ0 : List (Nat × Expr)}
    {kc : NestKey} {ps : List Expr} {st st' : RouteRK} {li ni : Nat}
    (hr : keyNiRK ops env h H L0 ni0 σ0 kc ps st = .ok (li, ni, st')) :
    LaysOnly st st' ∧ KeyNiRK st' h H L0 ni0 σ0 kc ps li ni := by
  unfold keyNiRK at hr
  obtain ⟨⟨li0, st1⟩, h1, hr⟩ := exceptBind_ok hr
  dsimp only at hr
  obtain ⟨lay', hl', hr⟩ := exceptBind_ok hr
  obtain ⟨σ, hσ, hr⟩ := exceptBind_ok hr
  have hp := pureRK_ok hr
  simp only [Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  have hl'' := unwrapOrRK_ok hl'
  obtain ⟨l, hl, hk⟩ := layIdxRK_key h1
  rw [hl''] at hl; obtain rfl := Option.some.inj hl
  obtain ⟨hn1, hn2, hn3⟩ := niIdxRK_ok li0 σ st1
  refine ⟨(layIdxRK_laysOnly h1).trans hn1, lay', σ, by rw [hn3]; exact hl'', hk, hσ, hn2⟩

/-- **The callee's node a leaf names** (`childRK`, option (c): the node the positivity check
used): the root at a member hole; the caller's node instance at an own hole; the key's node
with the use's bindings at a container key; at a flexible family, the node its entry names —
the binding's user's own node, or the binding's key's node with THAT use's bindings. -/
@[expose] def ChildKindRK (st : RouteRK) (I : InstRK) (H : HomeRK) (q : PairRK) (lay : LayRK) :
    LeafRK → Nat → Nat → Prop
  | .mem _, li, ni => (∃ lay', st.lays[li]? = some lay' ∧ LayKeyRK I.home none lay') ∧
      st.nis[ni]? = some (li, [])
  | .fam j, li, ni => ∃ ls0 σ0 nu b lu σu layU, st.nis[q.ni]? = some (ls0, σ0) ∧
      σ0[j]? = some (nu, b) ∧ st.nis[nu]? = some (lu, σu) ∧ st.lays[lu]? = some layU ∧
      ((∃ i ty, b.getAppFn = .fvar i ty ∧ li = lu ∧ ni = nu) ∨
        ∃ n us, b.getAppFn = .const n us ∧
          KeyNiRK st I.home H layU.L nu σu ⟨n, us, b.getAppArgs.map (rbK H.ctx layU.L)⟩
            b.getAppArgs li ni)
  | .own _, li, ni => li = q.lay ∧ ni = q.ni
  | .key kc ps, li, ni => ∃ ls0 σ0, st.nis[q.ni]? = some (ls0, σ0) ∧
      KeyNiRK st I.home H lay.L q.ni σ0 kc ps li ni

theorem ChildKindRK.mono {st st' : RouteRK} (hle : RouteLe st st') {I : InstRK} {H : HomeRK}
    {q : PairRK} {lay : LayRK} {kind : LeafRK} {li ni : Nat}
    (h : ChildKindRK st I H q lay kind li ni) : ChildKindRK st' I H q lay kind li ni := by
  cases kind with
  | mem t => obtain ⟨⟨l, h1, h2⟩, h3⟩ := h; exact ⟨⟨l, hle.lay h1, h2⟩, hle.ni h3⟩
  | fam j =>
    obtain ⟨ls0, σ0, nu, b, lu, σu, layU, h1, h2, h3, h4, h5⟩ := h
    refine ⟨ls0, σ0, nu, b, lu, σu, layU, hle.ni h1, h2, hle.ni h3, hle.lay h4, ?_⟩
    rcases h5 with h5 | ⟨n, us, hb, hk⟩
    · exact Or.inl h5
    · exact Or.inr ⟨n, us, hb, hk.mono hle⟩
  | own g => exact h
  | key kc ps => obtain ⟨ls0, σ0, h1, h2⟩ := h; exact ⟨ls0, σ0, hle.ni h1, h2.mono hle⟩

/-- **The callee's node, as run** (`childRK`). -/
theorem childRK_ok {I : InstRK} {H : HomeRK} {q : PairRK} {lay : LayRK} {kind : LeafRK}
    {cn : Name} {st st' : RouteRK} {li ni mi : Nat}
    (hr : childRK ops env I H q lay kind cn st = .ok (li, ni, mi, st')) :
    LaysOnly st st' ∧ ∃ lay', st'.lays[li]? = some lay' ∧
      lay'.mems.findIdx? (· == cn) = some mi ∧ ChildKindRK st' I H q lay kind li ni := by
  unfold childRK at hr
  -- the tail: the layout and the member
  have tail : ∀ {x : Nat × Nat × RouteRK},
      (do
        let lay' ← unwrapOr x.2.2.lays[x.1]? (.internal "nested route: layout")
        let mi ← unwrapOr (lay'.mems.findIdx? (· == cn)) (.internal "nested route: node member")
        pure (x.1, x.2.1, mi, x.2.2) : CheckM (Nat × Nat × Nat × RouteRK)) = .ok (li, ni, mi, st') →
      x = (li, ni, st') ∧ ∃ lay', st'.lays[li]? = some lay' ∧
        lay'.mems.findIdx? (· == cn) = some mi := by
    intro x h
    obtain ⟨lay', hl', h⟩ := exceptBind_ok h
    obtain ⟨mi0, hmi, h⟩ := exceptBind_ok h
    have hp := pureRK_ok h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨h1, h2, rfl, h4⟩ := hp
    obtain ⟨a, b, c⟩ := x
    simp only at h1 h2 h4
    subst h1 h2 h4
    exact ⟨rfl, lay', unwrapOrRK_ok hl', unwrapOrRK_ok hmi⟩
  have fin : ∀ {x : Nat × Nat × RouteRK}, x = (li, ni, st') →
      (LaysOnly st x.2.2 ∧ ChildKindRK x.2.2 I H q lay kind x.1 x.2.1) →
      (∃ lay', st'.lays[li]? = some lay' ∧ lay'.mems.findIdx? (· == cn) = some mi) →
      LaysOnly st st' ∧ ∃ lay', st'.lays[li]? = some lay' ∧
        lay'.mems.findIdx? (· == cn) = some mi ∧ ChildKindRK st' I H q lay kind li ni := by
    rintro x rfl ⟨h1, h2⟩ ⟨lay', h3, h4⟩
    exact ⟨h1, lay', h3, h4, h2⟩
  cases kind with
  | mem t =>
    dsimp only at hr
    obtain ⟨⟨l0, s0⟩, hl, hr⟩ := exceptBind_ok hr
    obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
    obtain rfl := (pureRK_ok hx).symm
    obtain ⟨hx, hlm⟩ := tail hr
    refine fin hx ?_ hlm
    obtain ⟨hn1, hn2, hn3⟩ := niIdxRK_ok l0 [] s0
    obtain ⟨l, hl0, hk⟩ := layIdxRK_key hl
    exact ⟨(layIdxRK_laysOnly hl).trans hn1, ⟨l, by rw [hn3]; exact hl0, hk⟩, hn2⟩
  | fam j =>
    dsimp only at hr
    obtain ⟨⟨ls0, σ0⟩, e1, hr⟩ := exceptBind_ok hr
    obtain ⟨⟨nu, b⟩, e2, hr⟩ := exceptBind_ok hr
    obtain ⟨⟨lu, σu⟩, e3, hr⟩ := exceptBind_ok hr
    obtain ⟨layU, e4, hr⟩ := exceptBind_ok hr
    replace e1 := unwrapOrRK_ok e1
    replace e2 := unwrapOrRK_ok e2
    replace e3 := unwrapOrRK_ok e3
    replace e4 := unwrapOrRK_ok e4
    split at hr
    · next i ty hb =>
      obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
      obtain rfl := (pureRK_ok hx).symm
      obtain ⟨hx', hlm⟩ := tail hr
      exact fin hx' ⟨LaysOnly.refl _, ls0, σ0, nu, b, lu, σu, layU, e1, e2, e3, e4,
        Or.inl ⟨i, ty, hb, rfl, rfl⟩⟩ hlm
    · next n us hb =>
      obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
      obtain ⟨hx', hlm⟩ := tail hr
      refine fin hx' ?_ hlm
      obtain ⟨a, c, d⟩ := x
      obtain ⟨hlo, hk⟩ := keyNiRK_ok hx
      have hle := hlo.le
      exact ⟨hlo, ls0, σ0, nu, b, lu, σu, layU, hle.ni e1, e2, hle.ni e3, hle.lay e4,
        Or.inr ⟨n, us, hb, hk⟩⟩
    · obtain ⟨_, h, _⟩ := exceptBind_ok hr
      exact absurd h throwRK_ne_ok
  | own g =>
    dsimp only at hr
    obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
    obtain rfl := (pureRK_ok hx).symm
    obtain ⟨hx', hlm⟩ := tail hr
    exact fin hx' ⟨LaysOnly.refl _, rfl, rfl⟩ hlm
  | key kc ps =>
    dsimp only at hr
    obtain ⟨⟨ls0, σ0⟩, e1, hr⟩ := exceptBind_ok hr
    replace e1 := unwrapOrRK_ok e1
    obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
    obtain ⟨hx', hlm⟩ := tail hr
    refine fin hx' ?_ hlm
    obtain ⟨a, c, d⟩ := x
    obtain ⟨hlo, hk⟩ := keyNiRK_ok hx
    exact ⟨hlo, ls0, σ0, hlo.le.ni e1, hk⟩

/-! ## The invariants of the state -/

/-- Every home is `homeRK`'s at some class, recorded under its names. -/
@[expose] def HomesOkRK (fe : FEnv) (p : BlockShape) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (st : RouteRK) : Prop :=
  st.homeNames.size = st.homes.size ∧
    (∀ (h : Nat) H, st.homes[h]? = some H →
      H.ctx.names = st.homeNames[h]?.getD [] ∧ ∃ M, homeRK (m := CheckM) fe p cvTas ctorsAs M = .ok H)

/-- **Every layout is built at its home**: the root's, or a container key's
(`contLayRK`, the positivity check's `nestLayoutK`). -/
@[expose] def LaysOkRK (ops : CheckerOps CheckM) (env : Env) (st : RouteRK) : Prop :=
  ∀ (i : Nat) l, st.lays[i]? = some l → ∃ H, st.homes[l.home]? = some H ∧
    ((l.key = none ∧ rootLayRK ops env l.home H = .ok l) ∨
      ∃ kc, l.key = some kc ∧ contLayRK ops env l.home H kc = .ok l)

theorem layIdxRK_laysOk {h : Nat} {key : Option NestKey} {st st' : RouteRK} {i : Nat}
    (hL : LaysOkRK ops env st) (hr : layIdxRK ops env h key st = .ok (i, st')) :
    LaysOkRK ops env st' := by
  obtain ⟨-, hH, -, -, -, -, -, H, l, hHh, -, hk⟩ := layIdxRK_ok hr
  rcases hk with ⟨rfl, -⟩ | ⟨rfl, hlays, hroot, hcont⟩
  · exact hL
  unfold LaysOkRK
  intro j l' hl'
  rw [hlays] at hl'
  rw [hH]
  rcases Nat.lt_or_ge j st.lays.size with hj | hj
  · rw [Array.getElem?_push_lt hj] at hl'
    exact hL j l' (by rw [Array.getElem?_eq_getElem hj]; exact hl')
  · have hj' : j = st.lays.size := by
      rcases Nat.lt_or_ge j (st.lays.size + 1) with h1 | h1
      · omega
      · rw [Array.getElem?_eq_none (by simp; omega)] at hl'; exact absurd hl' (by simp)
    subst hj'
    rw [Array.getElem?_push_size] at hl'
    obtain rfl := Option.some.inj hl'
    cases key with
    | none =>
      have hr0 := hroot rfl
      obtain ⟨hh, hk0⟩ := rootLayRK_ok hr0
      rw [hh]
      exact ⟨H, hHh, Or.inl ⟨hk0, hr0⟩⟩
    | some kc =>
      have hr0 := hcont kc rfl
      obtain ⟨hh, hk0⟩ := contLayRK_ok hr0
      rw [hh]
      exact ⟨H, hHh, Or.inr ⟨kc, hk0, hr0⟩⟩

theorem niIdxRK_laysOk {li : Nat} {σ : List (Nat × Expr)} {st : RouteRK}
    (hL : LaysOkRK ops env st) : LaysOkRK ops env (niIdxRK li σ st).2 := by
  obtain ⟨⟨h1, -, -, -, -, -, -, -⟩, -, h3⟩ := niIdxRK_ok li σ st
  unfold LaysOkRK at hL ⊢
  rw [h3, h1]; exact hL

theorem keyNiRK_laysOk {h : Nat} {H : HomeRK} {L0 : LayoutK} {ni0 : Nat}
    {σ0 : List (Nat × Expr)} {kc : NestKey} {ps : List Expr} {st st' : RouteRK} {li ni : Nat}
    (hL : LaysOkRK ops env st) (hr : keyNiRK ops env h H L0 ni0 σ0 kc ps st = .ok (li, ni, st')) :
    LaysOkRK ops env st' := by
  unfold keyNiRK at hr
  obtain ⟨⟨li0, st1⟩, h1, hr⟩ := exceptBind_ok hr
  dsimp only at hr
  obtain ⟨_, -, hr⟩ := exceptBind_ok hr
  obtain ⟨σ, -, hr⟩ := exceptBind_ok hr
  have hp := pureRK_ok hr
  simp only [Prod.mk.injEq] at hp
  obtain ⟨-, -, rfl⟩ := hp
  exact niIdxRK_laysOk (layIdxRK_laysOk hL h1)

theorem childRK_laysOk {I : InstRK} {H : HomeRK} {q : PairRK} {lay : LayRK} {kind : LeafRK}
    {cn : Name} {st st' : RouteRK} {li ni mi : Nat} (hL : LaysOkRK ops env st)
    (hr : childRK ops env I H q lay kind cn st = .ok (li, ni, mi, st')) : LaysOkRK ops env st' := by
  unfold childRK at hr
  have tail : ∀ {x : Nat × Nat × RouteRK},
      (do
        let lay' ← unwrapOr x.2.2.lays[x.1]? (.internal "nested route: layout")
        let mi ← unwrapOr (lay'.mems.findIdx? (· == cn)) (.internal "nested route: node member")
        pure (x.1, x.2.1, mi, x.2.2) : CheckM (Nat × Nat × Nat × RouteRK)) = .ok (li, ni, mi, st') →
      x.2.2 = st' := by
    intro x h
    obtain ⟨_, -, h⟩ := exceptBind_ok h
    obtain ⟨_, -, h⟩ := exceptBind_ok h
    have hp := pureRK_ok h
    simp only [Prod.mk.injEq] at hp
    exact hp.2.2.2
  cases kind with
  | mem t =>
    dsimp only at hr
    obtain ⟨⟨l0, s0⟩, hl, hr⟩ := exceptBind_ok hr
    obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
    obtain rfl := (pureRK_ok hx).symm
    rw [← tail hr]
    exact niIdxRK_laysOk (layIdxRK_laysOk hL hl)
  | fam j =>
    dsimp only at hr
    obtain ⟨_, -, hr⟩ := exceptBind_ok hr
    obtain ⟨_, -, hr⟩ := exceptBind_ok hr
    obtain ⟨_, -, hr⟩ := exceptBind_ok hr
    obtain ⟨_, -, hr⟩ := exceptBind_ok hr
    split at hr
    · obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
      obtain rfl := (pureRK_ok hx).symm
      rw [← tail hr]; exact hL
    · obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
      rw [← tail hr]
      obtain ⟨a, c, d⟩ := x
      exact keyNiRK_laysOk hL hx
    · obtain ⟨_, h, _⟩ := exceptBind_ok hr
      exact absurd h throwRK_ne_ok
  | own g =>
    dsimp only at hr
    obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
    obtain rfl := (pureRK_ok hx).symm
    rw [← tail hr]; exact hL
  | key kc ps =>
    dsimp only at hr
    obtain ⟨_, -, hr⟩ := exceptBind_ok hr
    obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
    rw [← tail hr]
    obtain ⟨a, c, d⟩ := x
    exact keyNiRK_laysOk hL hx

theorem keyNiRK_nisOk {h : Nat} {H : HomeRK} {L0 : LayoutK} {ni0 : Nat}
    {σ0 : List (Nat × Expr)} {kc : NestKey} {ps : List Expr} {st st' : RouteRK} {li ni : Nat}
    (hN : NisOkRK st)
    (hent : ∀ e : Nat × Expr, (e.1 = ni0 ∨ e ∈ σ0) → ∃ lu σu lu', st.nis[e.1]? = some (lu, σu) ∧
      st.lays[lu]? = some lu' ∧ lu'.home = h)
    (hr : keyNiRK ops env h H L0 ni0 σ0 kc ps st = .ok (li, ni, st')) : NisOkRK st' := by
  unfold keyNiRK at hr
  obtain ⟨⟨li0, st1⟩, h1, hr⟩ := exceptBind_ok hr
  dsimp only at hr
  obtain ⟨lay', hl', hr⟩ := exceptBind_ok hr
  obtain ⟨σ, hσ, hr⟩ := exceptBind_ok hr
  have hp := pureRK_ok hr
  simp only [Prod.mk.injEq] at hp
  obtain ⟨-, -, rfl⟩ := hp
  replace hl' := unwrapOrRK_ok hl'
  have hlo := layIdxRK_laysOnly h1
  have hN1 := hN.of_laysOnly hlo (layIdxRK_nis h1)
  obtain ⟨l, hl, hk⟩ := layIdxRK_key h1
  rw [hl'] at hl; obtain rfl := Option.some.inj hl
  have hhome : lay'.home = h := by
    rcases hk with hp | ⟨hh, -⟩
    · unfold layPredRK at hp; simp only [Bool.and_eq_true, beq_iff_eq] at hp; exact hp.1
    · exact hh
  refine niIdxRK_nisOk hN1 hl' fun e he => ?_
  obtain ⟨lu, σu, lu', e1, e2, e3⟩ := hent e (childCtxRK_entries hσ e he)
  exact ⟨lu, σu, lu', by rw [layIdxRK_nis h1]; exact e1, hlo.le.lay e2, e3.trans hhome.symm⟩

theorem childRK_nisOk {I : InstRK} {H : HomeRK} {q : PairRK} {lay : LayRK} {kind : LeafRK}
    {cn : Name} {st st' : RouteRK} {li ni mi : Nat} (hN : NisOkRK st)
    {σq : List (Nat × Expr)} (hσq : st.nis[q.ni]? = some (q.lay, σq))
    (hlay : st.lays[q.lay]? = some lay) (hhome : lay.home = I.home)
    (hr : childRK ops env I H q lay kind cn st = .ok (li, ni, mi, st')) : NisOkRK st' := by
  unfold childRK at hr
  have tail : ∀ {x : Nat × Nat × RouteRK},
      (do
        let lay' ← unwrapOr x.2.2.lays[x.1]? (.internal "nested route: layout")
        let mi ← unwrapOr (lay'.mems.findIdx? (· == cn)) (.internal "nested route: node member")
        pure (x.1, x.2.1, mi, x.2.2) : CheckM (Nat × Nat × Nat × RouteRK)) = .ok (li, ni, mi, st') →
      x.2.2 = st' := by
    intro x h
    obtain ⟨_, -, h⟩ := exceptBind_ok h
    obtain ⟨_, -, h⟩ := exceptBind_ok h
    have hp := pureRK_ok h
    simp only [Prod.mk.injEq] at hp
    exact hp.2.2.2
  -- the caller's entries are at its home
  obtain ⟨l0, hl0, hent0⟩ := hN q.ni q.lay σq hσq
  rw [hlay] at hl0; obtain rfl := Option.some.inj hl0
  cases kind with
  | mem t =>
    dsimp only at hr
    obtain ⟨⟨l0, s0⟩, hl, hr⟩ := exceptBind_ok hr
    obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
    obtain rfl := (pureRK_ok hx).symm
    rw [← tail hr]
    obtain ⟨l, hl1, -⟩ := layIdxRK_key hl
    exact niIdxRK_nisOk (hN.of_laysOnly (layIdxRK_laysOnly hl) (layIdxRK_nis hl)) hl1
      (fun e he => nomatch he)
  | fam j =>
    dsimp only at hr
    obtain ⟨⟨ls0, σ0⟩, e1, hr⟩ := exceptBind_ok hr
    replace e1 := unwrapOrRK_ok e1
    rw [hσq] at e1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
    obtain ⟨⟨nu, b⟩, e2, hr⟩ := exceptBind_ok hr
    obtain ⟨⟨lu, σu⟩, e3, hr⟩ := exceptBind_ok hr
    obtain ⟨layU, e4, hr⟩ := exceptBind_ok hr
    replace e2 := unwrapOrRK_ok e2
    replace e3 := unwrapOrRK_ok e3
    replace e4 := unwrapOrRK_ok e4
    split at hr
    · obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
      obtain rfl := (pureRK_ok hx).symm
      rw [← tail hr]; exact hN
    · obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
      rw [← tail hr]
      obtain ⟨a, c, d⟩ := x
      -- the entry's node instance is at the caller's home
      obtain ⟨-, lu', σu', lu'', f1, f2, f3⟩ := hent0 (nu, b) (List.mem_of_getElem? e2)
      rw [e3] at f1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj f1)
      rw [e4] at f2; obtain rfl := Option.some.inj f2
      obtain ⟨lU, hlU, hentU⟩ := hN nu lu σu e3
      rw [e4] at hlU; obtain rfl := Option.some.inj hlU
      refine keyNiRK_nisOk hN (fun e he => ?_) hx
      rcases he with he | he
      · exact ⟨lu, σu, layU, by rw [he]; exact e3, e4, f3.trans hhome⟩
      · obtain ⟨-, a1, a2, a3, g1, g2, g3⟩ := hentU e he
        exact ⟨a1, a2, a3, g1, g2, g3.trans (f3.trans hhome)⟩
    · obtain ⟨_, h, _⟩ := exceptBind_ok hr
      exact absurd h throwRK_ne_ok
  | own g =>
    dsimp only at hr
    obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
    obtain rfl := (pureRK_ok hx).symm
    rw [← tail hr]; exact hN
  | key kc ps =>
    dsimp only at hr
    obtain ⟨⟨ls0, σ0⟩, e1, hr⟩ := exceptBind_ok hr
    replace e1 := unwrapOrRK_ok e1
    rw [hσq] at e1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
    obtain ⟨x, hx, hr⟩ := exceptBind_ok hr
    rw [← tail hr]
    obtain ⟨a, c, d⟩ := x
    refine keyNiRK_nisOk hN (fun e he => ?_) hx
    rcases he with he | he
    · exact ⟨q.lay, σq, lay, by rw [he]; exact hσq, hlay, hhome⟩
    · obtain ⟨-, a1, a2, a3, g1, g2, g3⟩ := hent0 e he
      exact ⟨a1, a2, a3, g1, g2, g3.trans hhome⟩

end Ops

/-! ## A call's facts -/

section Call

variable (ops : CheckerOps CheckM) (env : Env) (Ms : List TargetMajor) (pc : List Expr)

/-- The canonical renaming of a class's parameters (`callRK`'s `rn`). -/
@[expose] def rnRK (pc : List Expr) (e : Expr) : Expr := e.replaceFVars fun i => pc[i]?

/-- The relocated holes of a call at a pair's layout. -/
@[expose] def hsRK (H : HomeRK) (I : InstRK) (lay : LayRK) (c : CallRK) : List Expr :=
  relocHolesRK H I c.base lay.holeTys []

/-- The renaming of a call's parameters to its rule prefix (`callRK`'s `rn`). -/
@[expose] def rnAtRK (c : CallRK) (e : Expr) : Expr := e.replaceFVars fun i => c.fvsPref[i]?

/-- **The per-component match of a call, as run** at a pair (`matchRK` against the leaf of
the called field's normal form at the pair's node, at the instance renamed to the call's
rule prefix, `instAtRK`; the canonical variables `pc` are not read). -/
@[expose] def MatchRunRK (ops : CheckerOps CheckM) (env : Env) (Ms : List TargetMajor)
    (_pc : List Expr) (st : RouteRK) (q : PairRK) (c : CallRK) (r : LeafRK × Name × List Expr) :
    Prop :=
  ∃ I H lay nf, st.insts[q.inst]? = some I ∧ st.homes[I.home]? = some H ∧
    st.lays[q.lay]? = some lay ∧
    ((lay.nfs.getD q.mem []).getD c.ctor [])[c.ih.field]? = some nf ∧
    matchRK ops env H (instAtRK c I) lay c.fvsPref.length (rnAtRK c) c.cn
      (Ms.getD c.ih.callee default) nf = .ok r

/-- **A strict call's typing, as run**: the node's crest field (holes relocated, at the
rule's field variables) and the callee's head (`headRK`: the leaf's hole or the callee's
inductive at the leaf's own relocated parameters) and the call's indices, under the call's
telescope, both inferred and defeq at the relocated depth — at the instance renamed to the
call's rule prefix. -/
@[expose] def TypingRunRK (st : RouteRK) (q : PairRK) (c : CallRK) (kind : LeafRK) : Prop :=
  ∃ I H lay nf crest fldH, st.insts[q.inst]? = some I ∧ st.homes[I.home]? = some H ∧
    st.lays[q.lay]? = some lay ∧
    ((lay.nfs.getD q.mem []).getD c.ctor [])[c.ih.field]? = some nf ∧
    (lay.crests.getD q.mem [])[c.ctor]? = some crest ∧
    ((targetPiDomsWith c.fvsF (relocRK H (instAtRK c I) (hsRK H (instAtRK c I) lay c)
      crest)).getD [])[c.ih.field]? = some fldH ∧
    (∃ ty, ops.inferType env (c.base + (hsRK H (instAtRK c I) lay c).length) fldH = .ok ty) ∧
    (∃ ty, ops.inferType env (c.base + (hsRK H (instAtRK c I) lay c).length)
      (Expr.mkPisOf (c.teles.getD c.ih.field [])
        (Expr.mkAppN (headRK H (instAtRK c I) lay (hsRK H (instAtRK c I) lay c)
            (Ms.getD c.ih.callee default) nf kind).1
          ((headRK H (instAtRK c I) lay (hsRK H (instAtRK c I) lay c)
            (Ms.getD c.ih.callee default) nf kind).2 ++ c.ih.idx)))
      = .ok ty) ∧
    ops.isDefEq env (c.base + (hsRK H (instAtRK c I) lay c).length) fldH
      (Expr.mkPisOf (c.teles.getD c.ih.field [])
        (Expr.mkAppN (headRK H (instAtRK c I) lay (hsRK H (instAtRK c I) lay c)
            (Ms.getD c.ih.callee default) nf kind).1
          ((headRK H (instAtRK c I) lay (hsRK H (instAtRK c I) lay c)
            (Ms.getD c.ih.callee default) nf kind).2 ++ c.ih.idx)))
      = .ok true

/-- **The callee's node at a call** (`childRK`): the layout `li` and member `mi` the leaf
names, from the caller pair's instance and layout. -/
@[expose] def CalleeAtRK (st : RouteRK) (q : PairRK) (kind : LeafRK) (cn : Name)
    (li ni mi : Nat) : Prop :=
  ∃ I H lay lay', st.insts[q.inst]? = some I ∧ st.homes[I.home]? = some H ∧
    st.lays[q.lay]? = some lay ∧ st.lays[li]? = some lay' ∧
    lay'.mems.findIdx? (· == cn) = some mi ∧ ChildKindRK st I H q lay kind li ni

/-- **A strict call, as run**: matched, typed, and its callee paired at the node its leaf
names. -/
@[expose] def StrictRunRK (st : RouteRK) (q : PairRK) (c : CallRK) : Prop :=
  ∃ kind cn dsC, MatchRunRK ops env Ms pc st q c (kind, cn, dsC) ∧
    TypingRunRK ops env Ms st q c kind ∧
    ∃ li ni mi sp, (⟨c.ih.callee, q.inst, li, mi, sp, ni⟩ : PairRK) ∈ st.pairs ∧
      CalleeAtRK st q kind cn li ni mi

end Call

theorem MatchRunRK.mono {ops : CheckerOps CheckM} {env : Env} {Ms : List TargetMajor}
    {pc : List Expr} {st st' : RouteRK} (hle : RouteLe st st') {q : PairRK} {c : CallRK}
    {r : LeafRK × Name × List Expr} (h : MatchRunRK ops env Ms pc st q c r) :
    MatchRunRK ops env Ms pc st' q c r := by
  obtain ⟨I, H, lay, nf, h1, h2, h3, h4, h5⟩ := h
  exact ⟨I, H, lay, nf, hle.inst h1, hle.home h2, hle.lay h3, h4, h5⟩

theorem TypingRunRK.mono {ops : CheckerOps CheckM} {env : Env} {Ms : List TargetMajor}
    {st st' : RouteRK} (hle : RouteLe st st') {q : PairRK} {c : CallRK} {kind : LeafRK}
    (h : TypingRunRK ops env Ms st q c kind) :
    TypingRunRK ops env Ms st' q c kind := by
  obtain ⟨I, H, lay, nf, crest, fldH, h1, h2, h3, h4, h5⟩ := h
  exact ⟨I, H, lay, nf, crest, fldH, hle.inst h1, hle.home h2, hle.lay h3, h4, h5⟩

theorem CalleeAtRK.mono {st st' : RouteRK} (hle : RouteLe st st') {q : PairRK} {kind : LeafRK}
    {cn : Name} {li ni mi : Nat} (h : CalleeAtRK st q kind cn li ni mi) :
    CalleeAtRK st' q kind cn li ni mi := by
  obtain ⟨I, H, lay, lay', h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨I, H, lay, lay', hle.inst h1, hle.home h2, hle.lay h3, hle.lay h4, h5, h6.mono hle⟩

theorem StrictRunRK.mono {ops : CheckerOps CheckM} {env : Env} {Ms : List TargetMajor}
    {pc : List Expr} {st st' : RouteRK} (hle : RouteLe st st') {q : PairRK} {c : CallRK}
    (h : StrictRunRK ops env Ms pc st q c) : StrictRunRK ops env Ms pc st' q c := by
  obtain ⟨kind, cn, dsC, h1, h2, li, ni, mi, sp, h3, h4⟩ := h
  exact ⟨kind, cn, dsC, h1.mono hle, h2.mono hle, li, ni, mi, sp, hle.pair h3, h4.mono hle⟩

end ConLeche

namespace ConLeche

/-- **A pair is valid**: its instance and layout exist, at one home; its member is its
class's inductive, whose constructors agree with the class's. -/
@[expose] def PairValidRK (Ms : List TargetMajor) (st : RouteRK) (q : PairRK) : Prop :=
  ∃ I lay, st.insts[q.inst]? = some I ∧ st.lays[q.lay]? = some lay ∧ lay.home = I.home ∧
    lay.mems[q.mem]? = some (Ms.getD q.cls default).ind ∧
    ctorsAgreeRK (Ms.getD q.cls default).ctors (lay.ctors.getD q.mem []) = true ∧
    ∃ σ, st.nis[q.ni]? = some (q.lay, σ)

section CallRun

variable {ops : CheckerOps CheckM} {env : Env} {Ms : List TargetMajor} {pc : List Expr}

/-- **The per-component match, as run** (`matchTryRK`): the leaf of the field's normal
form at the node, the callee's inductive and levels (`Level.isEquivList`), and the callee's
renamed parameters pairwise defeq to the leaf's read back at the instance, each inferred. -/
theorem matchTryRK_ok {H : HomeRK} {I : InstRK} {lay : LayRK} {d : Nat} {rn : Expr → Expr}
    {cnR : Name} {M'' : TargetMajor} {nf : Expr} {kind : LeafRK} {cn : Name} {dsC : List Expr}
    (h : matchTryRK ops env H I lay d rn cnR M'' nf = .ok (.ok (kind, cn, dsC))) :
    ∃ lvls ps, leafRK H lay nf = some (kind, cn, lvls, ps) ∧ M''.ind = cn ∧
      Level.isEquivList M''.lvls (lvls.map (lvl1RK H I)) = some true ∧
      dsC = M''.ds.map rn ∧
      paramsMismatchRK ops env d cnR dsC (ps.map (rbInstRK H I lay [])) = .ok none := by
  unfold matchTryRK at h
  split at h
  · next kind0 cn0 lvls ps hleaf =>
    dsimp only at h
    by_cases hc : (M''.ind == cn0 &&
        (Level.isEquivList M''.lvls (lvls.map (lvl1RK H I))).getD false) = true
    · rw [if_pos hc] at h
      obtain ⟨r, hpd, h⟩ := exceptBind_ok h
      cases r with
      | some msg => exact absurd (pureRK_ok h) (by simp)
      | none =>
        have hp := pureRK_ok h
        simp only [Except.ok.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl, rfl⟩ := hp
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        refine ⟨lvls, ps, hleaf, hc.1, ?_, rfl, hpd⟩
        have hc2 := hc.2
        cases he : Level.isEquivList M''.lvls (List.map (lvl1RK H I) lvls) with
        | none => rw [he] at hc2; simp at hc2
        | some b => rw [he] at hc2; simp at hc2; rw [hc2]
    · rw [if_neg hc] at h
      exact absurd (pureRK_ok h) (by simp)
  · exact absurd (pureRK_ok h) (by simp)

/-- `matchRK` is `matchTryRK`'s answer. -/
theorem matchRK_try {H : HomeRK} {I : InstRK} {lay : LayRK} {d : Nat} {rn : Expr → Expr}
    {cnR : Name} {M'' : TargetMajor} {nf : Expr} {r : LeafRK × Name × List Expr} :
    matchRK ops env H I lay d rn cnR M'' nf = .ok r ↔
      matchTryRK ops env H I lay d rn cnR M'' nf = .ok (.ok r) := by
  unfold matchRK
  constructor
  · intro h
    obtain ⟨x, hx, h⟩ := exceptBind_ok h
    cases x with
    | ok r' => rw [hx, pureRK_ok h]
    | error msg => exact absurd h throwRK_ne_ok
  · intro h
    rw [h]
    rfl

/-- **The per-component match, as run** (`matchRK`). -/
theorem matchRK_ok {H : HomeRK} {I : InstRK} {lay : LayRK} {d : Nat} {rn : Expr → Expr}
    {cnR : Name} {M'' : TargetMajor} {nf : Expr} {kind : LeafRK} {cn : Name} {dsC : List Expr}
    (h : matchRK ops env H I lay d rn cnR M'' nf = .ok (kind, cn, dsC)) :
    ∃ lvls ps, leafRK H lay nf = some (kind, cn, lvls, ps) ∧ M''.ind = cn ∧
      Level.isEquivList M''.lvls (lvls.map (lvl1RK H I)) = some true ∧
      dsC = M''.ds.map rn ∧
      paramsMismatchRK ops env d cnR dsC (ps.map (rbInstRK H I lay [])) = .ok none :=
  matchTryRK_ok (matchRK_try.mp h)

/-- What a call adds to the pairs: nothing, or its callee's pair, matched, at the node its
leaf names, with agreeing constructors. -/
@[expose] def CallAddRK (ops : CheckerOps CheckM) (env : Env) (Ms : List TargetMajor)
    (pc : List Expr) (st st' : RouteRK) (q : PairRK) (c : CallRK) : Prop :=
  st'.pairs = st.pairs ∨ ∃ kind cn dsC li ni mi sp,
    st'.pairs = st.pairs.push ⟨c.ih.callee, q.inst, li, mi, sp, ni⟩ ∧
    MatchRunRK ops env Ms pc st q c (kind, cn, dsC) ∧ CalleeAtRK st' q kind cn li ni mi ∧
    ∃ lay', st'.lays[li]? = some lay' ∧
      ctorsAgreeRK (Ms.getD c.ih.callee default).ctors (lay'.ctors.getD mi []) = true

/-- The strict arm of `callRK`, from its steps' runs. -/
theorem callStrict_fin {st st1 st2 st' : RouteRK} {q : PairRK} {c : CallRK} {I : InstRK}
    {H : HomeRK} {lay : LayRK} {kind : LeafRK} {cn : Name} {dsC : List Expr} {nf crest fldH : Expr}
    {li ni mi sp : Nat}
    (hI : st.insts[q.inst]? = some I) (hH : st.homes[I.home]? = some H)
    (hlay : st.lays[q.lay]? = some lay)
    (hnf : ((lay.nfs.getD q.mem []).getD c.ctor [])[c.ih.field]? = some nf)
    (hmr : MatchRunRK ops env Ms pc st q c (kind, cn, dsC))
    (hcrest : (lay.crests.getD q.mem [])[c.ctor]? = some crest)
    (hfld : ((targetPiDomsWith c.fvsF (relocRK H (instAtRK c I) (hsRK H (instAtRK c I) lay c) crest)).getD [])[c.ih.field]?
      = some fldH)
    (h1 : ∃ ty, ops.inferType env (c.base + (hsRK H (instAtRK c I) lay c).length) fldH = .ok ty)
    (h2 : ∃ ty, ops.inferType env (c.base + (hsRK H (instAtRK c I) lay c).length)
      (Expr.mkPisOf (c.teles.getD c.ih.field [])
        (Expr.mkAppN (headRK H (instAtRK c I) lay (hsRK H (instAtRK c I) lay c) (Ms.getD c.ih.callee default) nf kind).1
          ((headRK H (instAtRK c I) lay (hsRK H (instAtRK c I) lay c) (Ms.getD c.ih.callee default) nf kind).2 ++ c.ih.idx)))
      = .ok ty)
    (hb : ops.isDefEq env (c.base + (hsRK H (instAtRK c I) lay c).length) fldH
      (Expr.mkPisOf (c.teles.getD c.ih.field [])
        (Expr.mkAppN (headRK H (instAtRK c I) lay (hsRK H (instAtRK c I) lay c) (Ms.getD c.ih.callee default) nf kind).1
          ((headRK H (instAtRK c I) lay (hsRK H (instAtRK c I) lay c) (Ms.getD c.ih.callee default) nf kind).2 ++ c.ih.idx)))
      = .ok true)
    (hch : childRK ops env (instAtRK c I) H q lay kind cn st = .ok (li, ni, mi, st1))
    (hS2 : SpellsOnly st1 st2)
    (hr : addPairRK (m := CheckM) Ms true ⟨c.ih.callee, q.inst, li, mi, sp, ni⟩ st2 = .ok st') :
    RouteLe st st' ∧ st'.homes = st.homes ∧ st'.homeNames = st.homeNames ∧
      st'.insts = st.insts ∧ st'.next = st.next ∧
      (LaysOkRK ops env st → LaysOkRK ops env st') ∧ CallAddRK ops env Ms pc st st' q c ∧
      (true = true → StrictRunRK ops env Ms pc st' q c) ∧
      (NisOkRK st → PairValidRK Ms st q → NisOkRK st') := by
  have hnis : NisOkRK st → PairValidRK Ms st q → NisOkRK st' := by
    intro hN hv
    obtain ⟨I0, lay0, hI0, hlay0, hh0, -, -, σq, hσq⟩ := hv
    rw [hI] at hI0; obtain rfl := Option.some.inj hI0
    rw [hlay] at hlay0; obtain rfl := Option.some.inj hlay0
    have h1 := childRK_nisOk hN hσq hlay hh0 hch
    obtain ⟨-, -, -, hl2, -, -, -, hn2⟩ := hS2
    have h2 := h1.of_eq (by rw [hl2]; exact List.prefix_refl _) hn2
    obtain ⟨-, -, -, hl3, -, -, -⟩ := addPairRK_ok hr
    exact h2.of_eq (by rw [hl3]; exact List.prefix_refl _) (addPairRK_nis hr)
  obtain ⟨hL1, lay'', hl'', hmi, hck⟩ := childRK_ok hch
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := addPairRK_ok hr
  have hle1 := hL1.le
  have hle2 := hS2.le
  have hle3 := addPairRK_le hr
  have hle := hle1.trans (hle2.trans hle3)
  obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hL1
  obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := hS2
  have hca : CalleeAtRK st' q kind cn li ni mi := by
    refine ⟨I, H, lay, lay'', ?_, hle.home hH, hle.lay hlay, ?_, hmi, hck.mono (hle2.trans hle3)⟩
    · rw [a3, c3, b3]; exact hI
    · rw [a4, c4]; exact hl''
  have hty : TypingRunRK ops env Ms st q c kind :=
    ⟨I, H, lay, nf, crest, fldH, hI, hH, hlay, hnf, hcrest, hfld, h1, h2, hb⟩
  refine ⟨hle, by rw [a1, c1, b1], by rw [a2, c2, b2], by rw [a3, c3, b3],
    by rw [a5, c6, b5], fun hL => ?_, ?_, fun _ => ?_, hnis⟩
  · have := childRK_laysOk hL hch
    unfold LaysOkRK at this ⊢
    rw [a4, c4, a1, c1]; exact this
  · rcases a7 with ⟨h, -⟩ | ⟨h, lay3, hl3, hag⟩ | ⟨h, -⟩
    · left; rw [h, c5, b4]
    · right
      refine ⟨kind, cn, dsC, li, ni, mi, sp, by rw [h, c5, b4], hmr, hca, lay3, ?_, hag⟩
      rw [a4]; exact hl3
    · exact absurd h (by simp)
  · refine ⟨kind, cn, dsC, hmr.mono hle, hty.mono hle, li, ni, mi, sp, ?_, hca⟩
    rcases a7 with ⟨h, hmem⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact hmem
    · rw [h]; exact Array.mem_push_self
    · exact absurd h (by simp)

set_option maxHeartbeats 4000000 in
/-- **One call, as run** (`callRK`). -/
theorem callRK_ok {fam : TargetFamily} {strict : Bool} {q : PairRK} {c : CallRK}
    {st st' : RouteRK} (hr : callRK ops env fam Ms pc strict q c st = .ok st') :
    RouteLe st st' ∧ st'.homes = st.homes ∧ st'.homeNames = st.homeNames ∧
      st'.insts = st.insts ∧ st'.next = st.next ∧
      (LaysOkRK ops env st → LaysOkRK ops env st') ∧ CallAddRK ops env Ms pc st st' q c ∧
      (strict = true → StrictRunRK ops env Ms pc st' q c) ∧
      (NisOkRK st → PairValidRK Ms st q → NisOkRK st') := by
  unfold callRK at hr
  obtain ⟨I, hI, hr⟩ := exceptBind_ok hr
  obtain ⟨H, hH, hr⟩ := exceptBind_ok hr
  obtain ⟨lay, hlay, hr⟩ := exceptBind_ok hr
  obtain ⟨nf, hnf, hr⟩ := exceptBind_ok hr
  replace hI := unwrapOrRK_ok hI
  replace hH := unwrapOrRK_ok hH
  replace hlay := unwrapOrRK_ok hlay
  replace hnf := unwrapOrRK_ok hnf
  dsimp only at hr
  cases strict with
  | false =>
    simp only [Bool.not_false, if_true] at hr
    obtain ⟨r, hrr, hr⟩ := exceptBind_ok hr
    cases r with
    | error _ =>
      obtain rfl := pureRK_ok hr
      exact ⟨RouteLe.refl _, rfl, rfl, rfl, rfl, id, Or.inl rfl, fun h => (nomatch h),
        fun h _ => h⟩
    | ok x =>
      obtain ⟨kind, cn, dsC0⟩ := x
      have hm := matchRK_try.mpr hrr
      dsimp only at hr
      obtain ⟨⟨li, ni, mi, st1⟩, hch, hr⟩ := exceptBind_ok hr
      obtain ⟨⟨nfsS, LS⟩, -, hr⟩ := exceptBind_ok hr
      obtain ⟨nf53, -, hr⟩ := exceptBind_ok hr
      obtain ⟨lay', -, hr⟩ := exceptBind_ok hr
      obtain ⟨⟨sp, st2⟩, hcs, hr⟩ := exceptBind_ok hr
      dsimp only at hr
      obtain ⟨hL1, lay'', hl'', hmi, hck⟩ := childRK_ok hch
      have hS2 := calleeSpellRK_ok hcs
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := addPairRK_ok hr
      have hle1 := hL1.le
      have hle2 := hS2.le
      have hle3 := addPairRK_le hr
      have hle := hle1.trans (hle2.trans hle3)
      obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hL1
      obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := hS2
      have hmr : MatchRunRK ops env Ms pc st q c (kind, cn, dsC0) :=
        ⟨I, H, lay, nf, hI, hH, hlay, hnf, hm⟩
      have hnis : NisOkRK st → PairValidRK Ms st q → NisOkRK st' := by
        intro hN hv
        obtain ⟨I0, lay0, hI0, hlay0, hh0, -, -, σq, hσq⟩ := hv
        rw [hI] at hI0; obtain rfl := Option.some.inj hI0
        rw [hlay] at hlay0; obtain rfl := Option.some.inj hlay0
        have h1 := childRK_nisOk hN hσq hlay hh0 hch
        have h2 := h1.of_eq (by rw [c4]; exact List.prefix_refl _) ((calleeSpellRK_ok hcs).2.2.2.2.2.2.2)
        exact h2.of_eq (by rw [a4]; exact List.prefix_refl _) (addPairRK_nis hr)
      have hca : CalleeAtRK st' q kind cn li ni mi := by
        refine ⟨I, H, lay, lay'', ?_, hle.home hH, hle.lay hlay, ?_, hmi,
          hck.mono (hle2.trans hle3)⟩
        · rw [a3, c3, b3]; exact hI
        · rw [a4, c4]; exact hl''
      refine ⟨hle, by rw [a1, c1, b1], by rw [a2, c2, b2], by rw [a3, c3, b3],
        by rw [a5, c6, b5], fun hL => ?_, ?_, fun h => (nomatch h), hnis⟩
      · have := childRK_laysOk hL hch
        unfold LaysOkRK at this ⊢
        rw [a4, c4, a1, c1]; exact this
      · rcases a7 with ⟨h, -⟩ | ⟨h, lay3, hl3, hag⟩ | ⟨-, h⟩
        · left; rw [h, c5, b4]
        · right
          refine ⟨kind, cn, dsC0, li, ni, mi, sp, by rw [h, c5, b4], hmr, hca, lay3, ?_, hag⟩
          rw [a4]; exact hl3
        · left; rw [h, c5, b4]
  | true =>
    simp only [Bool.not_true] at hr
    obtain ⟨⟨kind, cn, dsC⟩, hm, hr⟩ := exceptBind_ok hr
    dsimp only at hr
    obtain ⟨crest, hcrest, hr⟩ := exceptBind_ok hr
    obtain ⟨fldH, hfld, hr⟩ := exceptBind_ok hr
    replace hcrest := unwrapOrRK_ok hcrest
    replace hfld := unwrapOrRK_ok hfld
    have hmr : MatchRunRK ops env Ms pc st q c (kind, cn, dsC) :=
      ⟨I, H, lay, nf, hI, hH, hlay, hnf, hm⟩
    obtain ⟨ty1, h1, hr⟩ := exceptBind_ok hr
    obtain ⟨ty2, h2, hr⟩ := exceptBind_ok hr
    obtain ⟨b, hb, hr⟩ := exceptBind_ok hr
    split at hr
    · next hbt =>
      subst hbt
      split at hr
      · split at hr
        · obtain ⟨_, -, hr⟩ := exceptBind_ok hr
          obtain ⟨_, -, hr⟩ := exceptBind_ok hr
          obtain ⟨_, -, hr⟩ := exceptBind_ok hr
          obtain ⟨⟨li, ni, mi, st1⟩, hch, hr⟩ := exceptBind_ok hr
          obtain ⟨lay', -, hr⟩ := exceptBind_ok hr
          obtain ⟨⟨sp, st2⟩, hcs, hr⟩ := exceptBind_ok hr
          exact callStrict_fin hI hH hlay hnf hmr hcrest hfld ⟨ty1, h1⟩ ⟨ty2, h2⟩ hb hch
            (calleeSpellRK_ok hcs) hr
        · exact absurd hr throwRK_ne_ok
      · exact absurd hr throwRK_ne_ok
    · obtain ⟨_, h, _⟩ := exceptBind_ok hr
      exact absurd h throwRK_ne_ok

end CallRun

/-! ## The pairs' invariant -/

section Inv

variable (ops : CheckerOps CheckM) (env : Env) (fe : FEnv) (p : BlockShape)
  (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
  (Ms : List TargetMajor) (pc : List Expr) (rk : List Nat) (hsF : List Bool)
  (calls : List (List CallRK))

/-- **A seed**: the root of its instance's home, at the class's own levels and (renamed)
parameters, its member the class's inductive in the home. -/
@[expose] def SeedRK (st : RouteRK) (q : PairRK) : Prop :=
  ∃ I H lay, st.insts[q.inst]? = some I ∧ st.homes[I.home]? = some H ∧
    st.lays[q.lay]? = some lay ∧ lay.key = none ∧
    I.us = (Ms.getD q.cls default).lvls ∧
    I.ds.map Expr.eraseFVarTys = ((Ms.getD q.cls default).ds.map (rnRK pc)).map Expr.eraseFVarTys ∧
    ∃ H', homeRK (m := CheckM) fe p cvTas ctorsAs (Ms.getD q.cls default) = .ok H' ∧
      H'.ctx.names = H.ctx.names

/-- **Where a pair comes from**: a seed, or the callee of a matched call of an earlier
pair, at the node the call's leaf names. -/
@[expose] def OriginRK (st : RouteRK) (q : PairRK) : Prop :=
  SeedRK fe p cvTas ctorsAs Ms pc st q ∨
    ∃ q0 ∈ st.pairs, ∃ c ∈ calls.getD q0.cls [], c.ih.callee = q.cls ∧ q.inst = q0.inst ∧
      ∃ kind cn dsC, MatchRunRK ops env Ms pc st q0 c (kind, cn, dsC) ∧
        CalleeAtRK st q0 kind cn q.lay q.ni q.mem

/-- **A pair processed**: every call of its class inside a hot component ran strictly. -/
@[expose] def DoneRK (st : RouteRK) (q : PairRK) : Prop :=
  ∀ c ∈ calls.getD q.cls [], (rk.getD c.ih.callee 0 == rk.getD q.cls 0) = true →
    hsF.getD q.cls false = true → StrictRunRK ops env Ms pc st q c

/-- **The route's invariant**: homes and layouts built, every pair valid and of known
origin, every pair before `next` processed. -/
@[expose] def GoodRK (st : RouteRK) : Prop :=
  HomesOkRK fe p cvTas ctorsAs st ∧ LaysOkRK ops env st ∧
    (∀ q ∈ st.pairs, PairValidRK Ms st q ∧ OriginRK ops env fe p cvTas ctorsAs Ms pc calls st q) ∧
    (∀ k, k < st.next → ∀ q, st.pairs[k]? = some q → DoneRK ops env Ms pc rk hsF calls st q) ∧
    st.next ≤ st.pairs.size ∧ NisOkRK st

end Inv

section InvMono

variable {ops : CheckerOps CheckM} {env : Env} {fe : FEnv} {p : BlockShape}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {Ms : List TargetMajor} {pc : List Expr} {rk : List Nat} {hsF : List Bool}
  {calls : List (List CallRK)} {st st' : RouteRK}

theorem PairValidRK.mono (hle : RouteLe st st') {q : PairRK} (h : PairValidRK Ms st q) :
    PairValidRK Ms st' q := by
  obtain ⟨I, lay, h1, h2, h3, h4, h5, σ, h6⟩ := h
  exact ⟨I, lay, hle.inst h1, hle.lay h2, h3, h4, h5, σ, hle.ni h6⟩

theorem SeedRK.mono (hle : RouteLe st st') {q : PairRK}
    (h : SeedRK fe p cvTas ctorsAs Ms pc st q) : SeedRK fe p cvTas ctorsAs Ms pc st' q := by
  obtain ⟨I, H, lay, h1, h2, h3, h4⟩ := h
  exact ⟨I, H, lay, hle.inst h1, hle.home h2, hle.lay h3, h4⟩

theorem OriginRK.mono (hle : RouteLe st st') {q : PairRK}
    (h : OriginRK ops env fe p cvTas ctorsAs Ms pc calls st q) :
    OriginRK ops env fe p cvTas ctorsAs Ms pc calls st' q := by
  rcases h with h | ⟨q0, hq0, c, hc, h1, h2, kind, cn, dsC, h3, h4⟩
  · exact Or.inl (h.mono hle)
  · exact Or.inr ⟨q0, hle.pair hq0, c, hc, h1, h2, kind, cn, dsC, h3.mono hle, h4.mono hle⟩

theorem DoneRK.mono (hle : RouteLe st st') {q : PairRK}
    (h : DoneRK ops env Ms pc rk hsF calls st q) : DoneRK ops env Ms pc rk hsF calls st' q :=
  fun c hc h1 h2 => (h c hc h1 h2).mono hle

end InvMono

section Loop

variable {ops : CheckerOps CheckM} {env : Env} {Ms : List TargetMajor} {pc : List Expr}

/-- **A callee's pair is valid**: its caller's instance, the layout the leaf names at
the caller's home, the leaf's inductive (the callee's, by the match) as its member. -/
theorem pairValid_callee {st : RouteRK} {q : PairRK} {c : CallRK} {kind : LeafRK} {cn : Name}
    {dsC : List Expr} {li ni mi sp : Nat} (hN : NisOkRK st) (hq : PairValidRK Ms st q)
    (hm : MatchRunRK ops env Ms pc st q c (kind, cn, dsC))
    (hca : CalleeAtRK st q kind cn li ni mi)
    (hag : ∃ lay', st.lays[li]? = some lay' ∧
      ctorsAgreeRK (Ms.getD c.ih.callee default).ctors (lay'.ctors.getD mi []) = true) :
    PairValidRK Ms st ⟨c.ih.callee, q.inst, li, mi, sp, ni⟩ := by
  obtain ⟨I, lay, hI, hlay, hhome, -, -, σq, hσq⟩ := hq
  obtain ⟨I', H, lay0, nf, hI', -, -, -, hmr⟩ := hm
  obtain ⟨I'', H', lay1, lay', hI'', -, hlay1, hl', hmi, hck⟩ := hca
  rw [hI] at hI' hI''
  obtain rfl := Option.some.inj hI'
  obtain rfl := Option.some.inj hI''
  rw [hlay] at hlay1
  obtain rfl := Option.some.inj hlay1
  obtain ⟨lvls, ps, -, hcn, -⟩ := matchRK_ok hmr
  obtain ⟨lay2, hl2, hag⟩ := hag
  rw [hl'] at hl2
  obtain rfl := Option.some.inj hl2
  have hkey : ∀ {key : Option NestKey}, LayKeyRK I.home key lay' → lay'.home = I.home := by
    intro key hk
    rcases hk with hp | ⟨hh, -⟩
    · unfold layPredRK at hp
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact hp.1
    · exact hh
  have hkni : ∀ {h : Nat} {H : HomeRK} {L0 : LayoutK} {ni0 : Nat} {σ0 : List (Nat × Expr)}
      {kc : NestKey} {ps : List Expr}, KeyNiRK st h H L0 ni0 σ0 kc ps li ni →
      (h = I.home) → lay'.home = I.home ∧ ∃ σ, st.nis[ni]? = some (li, σ) := by
    rintro h H L0 ni0 σ0 kc ps ⟨lay3, σ, h1, h2, -, h4⟩ rfl
    rw [hl'] at h1; obtain rfl := Option.some.inj h1
    exact ⟨hkey h2, σ, h4⟩
  obtain ⟨hh, σ, hσ⟩ : lay'.home = I.home ∧ ∃ σ, st.nis[ni]? = some (li, σ) := by
    cases kind with
    | mem t =>
      obtain ⟨⟨l, hl, hk⟩, hn⟩ := hck
      rw [hl'] at hl; obtain rfl := Option.some.inj hl
      exact ⟨hkey hk, [], hn⟩
    | fam j =>
      obtain ⟨ls0, σ0, nu, b, lu, σu, layU, h1, h2, h3, h4, h5⟩ := hck
      rw [hσq] at h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
      rcases h5 with ⟨i, ty, -, hli, hni⟩ | ⟨n, us, -, hk⟩
      · obtain ⟨l, hl, he⟩ := hN q.ni q.lay σq hσq
        rw [hlay] at hl; obtain rfl := Option.some.inj hl
        obtain ⟨-, lu', σu', lu'', e1, e2, e3⟩ := he (nu, b) (List.mem_of_getElem? h2)
        rw [h3] at e1
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
        rw [← hli, hl'] at e2; obtain rfl := Option.some.inj e2
        exact ⟨e3.trans hhome, σu, by rw [hni, hli]; exact h3⟩
      · exact hkni hk rfl
    | own g =>
      obtain ⟨rfl, rfl⟩ := hck
      rw [hlay] at hl'; obtain rfl := Option.some.inj hl'
      exact ⟨hhome, σq, hσq⟩
    | key kc ps =>
      obtain ⟨ls0, σ0, -, hk⟩ := hck
      exact hkni hk rfl
  refine ⟨I, lay', hI, hl', hh, ?_, hag, σ, hσ⟩
  obtain ⟨hlt, hbeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hmi
  rw [List.getElem?_eq_getElem hlt]
  simp only [beq_iff_eq] at hbeq
  rw [hbeq, hcn]

/-- **A pair's calls, as run** (`pairCallsRK`): the strict ones' facts, and every new
pair a matched callee of one of them. -/
theorem pairCallsRK_ok {fam : TargetFamily} {rk : List Nat} {hsF : List Bool} {q : PairRK} :
    ∀ {cs : List CallRK} {st st' : RouteRK},
    pairCallsRK ops env fam Ms pc rk hsF q cs st = .ok st' →
    RouteLe st st' ∧ st'.homes = st.homes ∧ st'.homeNames = st.homeNames ∧
      st'.insts = st.insts ∧ st'.next = st.next ∧
      (LaysOkRK ops env st → LaysOkRK ops env st') ∧
      (∀ c ∈ cs, (rk.getD c.ih.callee 0 == rk.getD q.cls 0) = true →
        hsF.getD q.cls false = true → StrictRunRK ops env Ms pc st' q c) ∧
      (∀ q' ∈ st'.pairs, q' ∈ st.pairs ∨ ∃ c ∈ cs, c.ih.callee = q'.cls ∧ q'.inst = q.inst ∧
        ∃ kind cn dsC, MatchRunRK ops env Ms pc st' q c (kind, cn, dsC) ∧
          CalleeAtRK st' q kind cn q'.lay q'.ni q'.mem ∧ ∃ lay', st'.lays[q'.lay]? = some lay' ∧
            ctorsAgreeRK (Ms.getD q'.cls default).ctors (lay'.ctors.getD q'.mem []) = true) ∧
      (NisOkRK st → PairValidRK Ms st q → NisOkRK st')
  | [], st, st', h => by
    unfold pairCallsRK at h
    obtain rfl := pureRK_ok h
    exact ⟨RouteLe.refl _, rfl, rfl, rfl, rfl, id, fun _ h => (nomatch h), fun q' h => Or.inl h,
      fun h _ => h⟩
  | c :: cs, st, st', h => by
    unfold pairCallsRK at h
    dsimp only at h
    have hsplit : ∃ st1, (if (rk.getD c.ih.callee 0 == rk.getD q.cls 0 && !hsF.getD q.cls false)
        = true then (pure st : CheckM RouteRK)
        else callRK ops env fam Ms pc (rk.getD c.ih.callee 0 == rk.getD q.cls 0) q c st) = .ok st1 ∧
        pairCallsRK ops env fam Ms pc rk hsF q cs st1 = .ok st' := by
      split at h
      · next hc => obtain ⟨st1, h1, h⟩ := exceptBind_ok h; exact ⟨st1, by rw [if_pos hc]; exact h1, h⟩
      · next hc => obtain ⟨st1, h1, h⟩ := exceptBind_ok h; exact ⟨st1, by rw [if_neg hc]; exact h1, h⟩
    obtain ⟨st1, h1, h⟩ := hsplit
    obtain ⟨le2, e1, e2, e3, e4, lays2, strict2, new2, nis2⟩ := pairCallsRK_ok h
    -- the head call
    have head : RouteLe st st1 ∧ st1.homes = st.homes ∧ st1.homeNames = st.homeNames ∧
        st1.insts = st.insts ∧ st1.next = st.next ∧
        (LaysOkRK ops env st → LaysOkRK ops env st1) ∧ CallAddRK ops env Ms pc st st1 q c ∧
        ((rk.getD c.ih.callee 0 == rk.getD q.cls 0) = true → hsF.getD q.cls false = true →
          StrictRunRK ops env Ms pc st1 q c) ∧
        (NisOkRK st → PairValidRK Ms st q → NisOkRK st1) := by
      split at h1
      · next hskip =>
        obtain rfl := pureRK_ok h1
        refine ⟨RouteLe.refl _, rfl, rfl, rfl, rfl, id, Or.inl rfl, fun h1 h2 => ?_, fun h _ => h⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hskip
        rw [hskip.2] at h2; exact absurd h2 (by simp)
      · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := callRK_ok h1
        exact ⟨a1, a2, a3, a4, a5, a6, a7, fun hi _ => a8 hi, a9⟩
    obtain ⟨le1, d1, d2, d3, d4, lays1, add1, strict1, nis1⟩ := head
    refine ⟨le1.trans le2, by rw [e1, d1], by rw [e2, d2], by rw [e3, d3], by rw [e4, d4],
      fun hL => lays2 (lays1 hL), ?_, ?_,
      fun hN hv => nis2 (nis1 hN hv) (hv.mono le1)⟩
    · intro c' hc' hi hh
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact (strict1 hi hh).mono le2
      · exact strict2 c' hc' hi hh
    · intro q' hq'
      rcases new2 q' hq' with hq1 | ⟨c', hc', rest⟩
      · rcases add1 with hsame | ⟨kind, cn, dsC, li, ni, mi, sp, hpush, hm, hca, lay', hl', hag⟩
        · left; rw [← hsame]; exact hq1
        · rw [hpush] at hq1
          rcases Array.mem_push.mp hq1 with hq1 | rfl
          · exact Or.inl hq1
          · exact Or.inr ⟨c, List.mem_cons_self, rfl, rfl, kind, cn, dsC, hm.mono (le1.trans le2),
              hca.mono le2, lay', le2.lay hl', hag⟩
      · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', rest⟩

theorem laysOkRK_homes {st st' : RouteRK} (hL : LaysOkRK ops env st)
    (hh : st.homes.toList <+: st'.homes.toList) (hl : st'.lays = st.lays) :
    LaysOkRK ops env st' := by
  unfold LaysOkRK at hL ⊢
  intro i l hil
  rw [hl] at hil
  obtain ⟨H, hH, rest⟩ := hL i l hil
  exact ⟨H, array_getElem?_of_prefix hh hH, rest⟩

theorem rootLayRK_mems {h : Nat} {H : HomeRK} {l : LayRK}
    (hr : rootLayRK ops env h H = .ok l) : l.mems = H.ctx.names := by
  unfold rootLayRK at hr
  obtain ⟨_, _, hr⟩ := exceptBind_ok hr
  obtain ⟨_, _, hr⟩ := exceptBind_ok hr
  obtain rfl := pureRK_ok hr
  rfl

/-- **The worklist, as run** (`routeLoopRK`): the invariant holds at the end, where every
pair has been processed. -/
theorem routeLoopRK_ok {fe : FEnv} {p : BlockShape} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {fam : TargetFamily} {rk : List Nat}
    {hsF : List Bool} {calls : List (List CallRK)} :
    ∀ {fuel : Nat} {st st' : RouteRK},
    GoodRK ops env fe p cvTas ctorsAs Ms pc rk hsF calls st →
    routeLoopRK ops env fam Ms pc rk hsF calls fuel st = .ok st' →
    GoodRK ops env fe p cvTas ctorsAs Ms pc rk hsF calls st' ∧ RouteLe st st' ∧
      st'.homes = st.homes ∧ st'.homeNames = st.homeNames ∧ st'.insts = st.insts ∧
      st'.pairs[st'.next]? = none
  | 0, _, _, _, h => absurd h throwRK_ne_ok
  | fuel + 1, st, st', hG, h => by
    unfold routeLoopRK at h
    split at h
    · next hnone =>
      obtain rfl := pureRK_ok h
      exact ⟨hG, RouteLe.refl _, rfl, rfl, rfl, hnone⟩
    · next q hq =>
      obtain ⟨st2, h2, h⟩ := exceptBind_ok h
      obtain ⟨hHo, hLo, hPo, hDo, hNx, hNi⟩ := hG
      have hqm : q ∈ st.pairs := Array.mem_of_getElem? hq
      obtain ⟨le2, e1, e2, e3, e4, lays2, strict2, new2, nis2⟩ := pairCallsRK_ok h2
      have le1 : RouteLe st { st with next := st.next + 1 } :=
        ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
          List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩
      have le := le1.trans le2
      have hNi2 : NisOkRK st2 := nis2 hNi (hPo q hqm).1
      have hG2 : GoodRK ops env fe p cvTas ctorsAs Ms pc rk hsF calls st2 := by
        refine ⟨?_, lays2 hLo, ?_, ?_, ?_, hNi2⟩
        · unfold HomesOkRK at hHo ⊢
          rw [e1, e2]; exact hHo
        · intro q' hq'
          rcases new2 q' hq' with hq1 | ⟨c, hc, hcal, hins, kind, cn, dsC, hm, hca, lay', hl', hag⟩
          · obtain ⟨hv, ho⟩ := hPo q' hq1
            exact ⟨hv.mono le, ho.mono le⟩
          · obtain ⟨cls, inst, li, mi, sp, ni⟩ := q'
            simp only at hcal hins hca hl' hag
            subst hcal hins
            have hvq := (hPo q hqm).1.mono le
            exact ⟨pairValid_callee hNi2 hvq hm hca ⟨lay', hl', hag⟩,
              Or.inr ⟨q, le.pair hqm, c, hc, rfl, rfl, kind, cn, dsC, hm, hca⟩⟩
        · intro k hk q'' hq''
          rw [e4] at hk
          simp only at hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · obtain ⟨q3, hq3⟩ : ∃ q3, st.pairs[k]? = some q3 := by
              rcases h3 : st.pairs[k]? with _ | q3
              · have : k < st.pairs.size := by
                  have := (Array.getElem?_eq_some_iff.mp hq).1
                  have hn : k < st.next := hk
                  omega
                rw [Array.getElem?_eq_getElem this] at h3; exact absurd h3 (by simp)
              · exact ⟨q3, rfl⟩
            have := le.pairAt hq3
            rw [hq''] at this
            obtain rfl := Option.some.inj this
            exact (hDo k hk q'' hq3).mono le
          · have := le.pairAt hq
            rw [hq''] at this
            obtain rfl := Option.some.inj this
            exact fun c hc hi hh => strict2 c hc hi hh
        · rw [e4]
          have h1 := (Array.getElem?_eq_some_iff.mp hq).1
          have h2 := le2.pairs.length_le
          simp only [Array.length_toList] at h2
          show st.next + 1 ≤ st2.pairs.size
          omega
      obtain ⟨hG', le', f1, f2, f3, hnone⟩ := routeLoopRK_ok hG2 h
      exact ⟨hG', le.trans le', by rw [f1, e1], by rw [f2, e2], by rw [f3, e3], hnone⟩

/-- **A home, found or read, keeps the homes' invariant** and names a home read at the
class's home's names. -/
theorem homeIdxRK_homesOk {fe : FEnv} {p : BlockShape} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {M : TargetMajor} {st st' : RouteRK} {h : Nat}
    (hHo : HomesOkRK fe p cvTas ctorsAs st)
    (hr : homeIdxRK (m := CheckM) fe p cvTas ctorsAs M st = .ok (h, st')) :
    HomesOkRK fe p cvTas ctorsAs st' ∧ ∃ H, st'.homes[h]? = some H ∧
      ∃ H', homeRK (m := CheckM) fe p cvTas ctorsAs M = .ok H' ∧ H'.ctx.names = H.ctx.names := by
  obtain ⟨-, -, -, -, -, -, H0, hH0, hhome⟩ := homeIdxRK_ok hr
  obtain ⟨hsz, hall⟩ := hHo
  rcases hhome with ⟨e1, e2, hn⟩ | ⟨e1, e2, rfl⟩
  · refine ⟨by unfold HomesOkRK; rw [e1, e2]; exact ⟨hsz, hall⟩, ?_⟩
    have hlt : h < st.homes.size := by
      rw [← hsz]; exact (Array.getElem?_eq_some_iff.mp hn).1
    refine ⟨st.homes[h], by rw [e1]; exact Array.getElem?_eq_getElem hlt, H0, hH0, ?_⟩
    have := (hall h st.homes[h] (Array.getElem?_eq_getElem hlt)).1
    rw [this, hn]; rfl
  · refine ⟨⟨by rw [e1, e2]; simp [hsz], fun h' H' hH' => ?_⟩, H0, by rw [e1]; simp, H0, hH0, rfl⟩
    rw [e1] at hH'
    rw [e2]
    rcases Nat.lt_or_ge h' st.homes.size with hlt | hge
    · rw [Array.getElem?_push_lt hlt] at hH'
      rw [Array.getElem?_push_lt (by rw [hsz]; exact hlt)]
      have := hall h' H' (by rw [Array.getElem?_eq_getElem hlt]; exact hH')
      rw [Array.getElem?_eq_getElem (by rw [hsz]; exact hlt)] at this
      exact this
    · have : h' = st.homes.size := by
        rcases Nat.lt_or_ge h' (st.homes.size + 1) with h1 | h1
        · omega
        · rw [Array.getElem?_eq_none (by simp; omega)] at hH'; exact absurd hH' (by simp)
      subst this
      rw [Array.getElem?_push_size] at hH'
      obtain rfl := Option.some.inj hH'
      rw [← hsz, Array.getElem?_push_size]
      exact ⟨rfl, _, hH0⟩

/-- **One seed's pair, from its steps' runs**: the invariant kept. -/
theorem seedStep_good {fe : FEnv} {p : BlockShape} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {rk : List Nat} {hsF : List Bool}
    {calls : List (List CallRK)} {st1 st2 st3 st4 : RouteRK} {c ii li t hh : Nat}
    {I : InstRK} {H : HomeRK}
    (hG1 : GoodRK ops fe.env fe p cvTas ctorsAs Ms pc rk hsF calls st1)
    (hname : ∀ H1, st1.homes[hh]? = some H1 → ∃ H', homeRK (m := CheckM) fe p cvTas ctorsAs
      (Ms.getD c default) = .ok H' ∧ H'.ctx.names = H1.ctx.names)
    (e1 : st2.homes = st1.homes) (e2 : st2.homeNames = st1.homeNames) (e3 : st2.lays = st1.lays)
    (e4 : st2.pairs = st1.pairs) (e5 : st2.next = st1.next) (e6 : st2.spells = st1.spells)
    (e7 : st2.nis = st1.nis)
    (ei : st1.insts.toList <+: st2.insts.toList)
    (hI : st2.insts[ii]? = some I) (hIh : I.home = hh) (hIus : I.us = (Ms.getD c default).lvls)
    (hIds : I.ds.map Expr.eraseFVarTys =
      ((Ms.getD c default).ds.map (rnRK pc)).map Expr.eraseFVarTys)
    (h3 : layIdxRK ops fe.env hh none st2 = .ok (li, st3))
    (hH : (niIdxRK li [] st3).2.homes[hh]? = some H)
    (ht : H.ctx.names.findIdx? (· == (Ms.getD c default).ind) = some t)
    (h4 : addPairRK (m := CheckM) Ms true ⟨c, ii, li, t, 0, (niIdxRK li [] st3).1⟩
      (niIdxRK li [] st3).2 = .ok st4) :
    GoodRK ops fe.env fe p cvTas ctorsAs Ms pc rk hsF calls st4 ∧ RouteLe st1 st4 ∧
      st4.next = st1.next := by
  obtain ⟨hHo, hLo, hPo, hDo, hNx, hNi⟩ := hG1
  have le12 : RouteLe st1 st2 :=
    ⟨by rw [e1]; exact List.prefix_refl _, by rw [e2]; exact List.prefix_refl _, ei,
      by rw [e3]; exact List.prefix_refl _, by rw [e4]; exact List.prefix_refl _,
      by rw [e6]; exact List.prefix_refl _, by rw [e7]; exact List.prefix_refl _⟩
  obtain ⟨le3, f1, f2, f3, f4, f5, f6, -⟩ := layIdxRK_ok h3
  have f7 := layIdxRK_nis h3
  obtain ⟨lay, hlay, hkey⟩ := layIdxRK_key h3
  obtain ⟨hn1, hn2, hn3⟩ := niIdxRK_ok li [] st3
  generalize hn : niIdxRK li [] st3 = n3 at hH h4 hn1 hn2 hn3
  obtain ⟨ni, st3'⟩ := n3
  simp only at hH h4 hn1 hn2 hn3
  have le3' := hn1.le
  obtain ⟨g1, g2, g3, g4, g5, g6, -, -⟩ := hn1
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := addPairRK_ok h4
  have le4 := addPairRK_le h4
  have le := le12.trans (le3.trans (le3'.trans le4))
  have hL2 : LaysOkRK ops fe.env st2 := by
    unfold LaysOkRK at hLo ⊢; rw [e3, e1]; exact hLo
  have hL3 := layIdxRK_laysOk hL2 h3
  -- the new pair's layout is its home's root
  have hlay4 : st4.lays[li]? = some lay := by rw [a4, hn3]; exact hlay
  have hroot : lay.home = hh ∧ lay.key = none ∧ lay.mems = H.ctx.names := by
    obtain ⟨H', hH', hk⟩ := hL3 li lay hlay
    have hlh : lay.home = hh := by
      rcases hkey with hp | ⟨hh', -⟩
      · unfold layPredRK at hp; simp only [Bool.and_eq_true, beq_iff_eq] at hp; exact hp.1
      · exact hh'
    rw [hlh, ← g1, hH] at hH'
    obtain rfl := Option.some.inj hH'
    rcases hk with ⟨hk0, hr0⟩ | ⟨kc, hk0, -⟩
    · exact ⟨hlh, hk0, rootLayRK_mems hr0⟩
    · exfalso
      rcases hkey with hp | ⟨-, hk'⟩
      · unfold layPredRK at hp; rw [hk0] at hp; simp at hp
      · rw [hk0] at hk'; exact absurd hk' (by simp)
  obtain ⟨hlh, hlk, hlm⟩ := hroot
  have hH1 : st1.homes[hh]? = some H := by rw [← e1, ← f1, ← g1]; exact hH
  obtain ⟨H', hH', hHn⟩ := hname H hH1
  -- the node instances
  have hNi2 : NisOkRK st2 := hNi.of_eq (by rw [e3]; exact List.prefix_refl _) e7
  have hNi3 : NisOkRK st3 := hNi2.of_laysOnly (layIdxRK_laysOnly h3) f7
  have hNi3' : NisOkRK st3' := by
    have := niIdxRK_nisOk (li := li) (σ := []) hNi3 hlay (fun e he => nomatch he)
    rw [hn] at this; exact this
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, le, by rw [a5, g5, f4, e5]⟩
  · unfold HomesOkRK at hHo ⊢; rw [a1, a2, g1, g2, f1, f6, e1, e2]; exact hHo
  · unfold LaysOkRK at hL3 ⊢; rw [a4, a1, g1, hn3]; exact hL3
  · intro q hq
    have hold : q ∈ st3'.pairs → PairValidRK Ms st4 q ∧
        OriginRK ops fe.env fe p cvTas ctorsAs Ms pc calls st4 q := by
      intro hq3
      rw [g4, f3, e4] at hq3
      obtain ⟨hv, ho⟩ := hPo q hq3
      exact ⟨hv.mono le, ho.mono le⟩
    rcases a7 with ⟨h, -⟩ | ⟨h, lay', hl', hag⟩ | ⟨h, -⟩
    · exact hold (by rw [← h]; exact hq)
    · rw [h] at hq
      rcases Array.mem_push.mp hq with hq | rfl
      · exact hold hq
      · rw [hn3, hlay] at hl'
        obtain rfl := Option.some.inj hl'
        have hI4 : st4.insts[ii]? = some I := by rw [a3, g3, f2]; exact hI
        refine ⟨⟨I, lay, hI4, hlay4, by rw [hlh, hIh], ?_, hag, [], ?_⟩, Or.inl ?_⟩
        · obtain ⟨hlt, hbeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp ht
          simp only [beq_iff_eq] at hbeq
          rw [hlm, List.getElem?_eq_getElem hlt, hbeq]
        · exact le4.ni hn2
        · refine ⟨I, H, lay, hI4, ?_, hlay4, hlk, hIus, hIds, H', hH', hHn⟩
          rw [a1, hIh]; exact hH
    · exact absurd h (by simp)
  · intro k hk q hq
    rw [a5, g5, f4, e5] at hk
    obtain ⟨q1, hq1⟩ : ∃ q1, st1.pairs[k]? = some q1 :=
      ⟨st1.pairs[k]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
    have := le.pairAt hq1
    rw [hq] at this
    obtain rfl := Option.some.inj this
    exact (hDo k hk q hq1).mono le
  · have h2 := le.pairs.length_le
    simp only [Array.length_toList] at h2
    rw [a5, g5, f4, e5]; omega
  · exact hNi3'.of_eq (by rw [a4]; exact List.prefix_refl _) (addPairRK_nis h4)

/-- **The seeds, as run** (`seedsRK`): each at its home's root, at its own instance. -/
theorem seedsRK_ok {fe : FEnv} {p : BlockShape} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {rk : List Nat} {hsF : List Bool}
    {calls : List (List CallRK)} :
    ∀ {cs : List Nat} {st st' : RouteRK},
    GoodRK ops fe.env fe p cvTas ctorsAs Ms pc rk hsF calls st →
    seedsRK ops fe p cvTas ctorsAs Ms pc cs st = .ok st' →
    GoodRK ops fe.env fe p cvTas ctorsAs Ms pc rk hsF calls st' ∧ RouteLe st st' ∧
      st'.next = st.next
  | [], st, st', hG, h => by
    unfold seedsRK at h
    obtain rfl := pureRK_ok h
    exact ⟨hG, RouteLe.refl _, rfl⟩
  | c :: cs, st, st', hG, h => by
    unfold seedsRK at h
    dsimp only at h
    obtain ⟨⟨hh, st1⟩, h1, h⟩ := exceptBind_ok h
    dsimp only at h
    obtain ⟨le1, l1, i1, p1, n1, s1, -⟩ := homeIdxRK_ok h1
    obtain ⟨hHo, hLo, hPo, hDo, hNx, hNi⟩ := hG
    have nis1 := homeIdxRK_nis h1
    obtain ⟨hHo1, -⟩ := homeIdxRK_homesOk hHo h1
    have hname : ∀ H1, st1.homes[hh]? = some H1 → ∃ H', homeRK (m := CheckM) fe p cvTas
        ctorsAs (Ms.getD c default) = .ok H' ∧ H'.ctx.names = H1.ctx.names := by
      intro H1 hH1
      obtain ⟨-, H, hH, H', hH', hn⟩ := homeIdxRK_homesOk hHo h1
      rw [hH] at hH1; obtain rfl := Option.some.inj hH1
      exact ⟨H', hH', hn⟩
    have hG1 : GoodRK ops fe.env fe p cvTas ctorsAs Ms pc rk hsF calls st1 := by
      refine ⟨hHo1, laysOkRK_homes hLo le1.homes l1, fun q hq => ?_, fun k hk q hq => ?_, ?_,
        hNi.of_eq (by rw [l1]; exact List.prefix_refl _) nis1⟩
      · rw [p1] at hq
        obtain ⟨hv, ho⟩ := hPo q hq
        exact ⟨hv.mono le1, ho.mono le1⟩
      · rw [n1] at hk
        rw [p1] at hq
        exact (hDo k hk q hq).mono le1
      · rw [n1, p1]; exact hNx
    have hds : ((Ms.getD c default).ds.map (fun e => e.replaceFVars fun i => pc[i]?))
        = (Ms.getD c default).ds.map (rnRK pc) := rfl
    split at h
    · next ii0 hii =>
      obtain ⟨hlt, hbeq, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hii
      simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
      obtain ⟨⟨li, st3⟩, h3, h⟩ := exceptBind_ok h
      obtain ⟨H, hH, h⟩ := exceptBind_ok h
      obtain ⟨t, ht, h⟩ := exceptBind_ok h
      obtain ⟨st4, h4, h⟩ := exceptBind_ok h
      obtain ⟨hG4, le4, n4⟩ := seedStep_good hG1 hname rfl rfl rfl rfl rfl rfl rfl
        (List.prefix_refl _) (Array.getElem?_eq_getElem hlt) hbeq.1.1 hbeq.1.2
        (by rw [hbeq.2]; rfl) h3 (unwrapOrRK_ok hH) (unwrapOrRK_ok ht) h4
      obtain ⟨hG', le', n'⟩ := seedsRK_ok hG4 h
      exact ⟨hG', le1.trans (le4.trans le'), by rw [n', n4, n1]⟩
    · obtain ⟨⟨li, st3⟩, h3, h⟩ := exceptBind_ok h
      obtain ⟨H, hH, h⟩ := exceptBind_ok h
      obtain ⟨t, ht, h⟩ := exceptBind_ok h
      obtain ⟨st4, h4, h⟩ := exceptBind_ok h
      dsimp only at h3 h4
      let I0 : InstRK := ⟨hh, (Ms.getD c default).lvls, (Ms.getD c default).ds.map (rnRK pc)⟩
      obtain ⟨hG4, le4, n4⟩ := seedStep_good (st2 := { st1 with insts := st1.insts.push I0 })
        hG1 hname rfl rfl rfl rfl rfl rfl rfl
        (array_prefix_push _ _) Array.getElem?_push_size rfl rfl rfl h3 (unwrapOrRK_ok hH)
        (unwrapOrRK_ok ht) h4
      obtain ⟨hG', le', n'⟩ := seedsRK_ok hG4 h
      exact ⟨hG', le1.trans (le4.trans le'), by rw [n', n4, n1]⟩

/-- **The positivity re-run on the homes** (`homesPosRK`), per home: the key-named check
succeeded there, and every container layout the route built at the home is a node of the
run (its key in the run's cache). -/
theorem homesPosRK_ok {env : Env} {lays : List LayRK} :
    ∀ {h0 : Nat} {Hs : List HomeRK}, homesPosRK ops env lays h0 Hs = .ok () →
      ∀ (i : Nat) (H : HomeRK), Hs[i]? = some H → ∃ ks ns pst,
        nestBlockCtorsGoK ops env H.ctx H.holes H.ctors {} = .ok (ks, ns, pst) ∧
        ∀ l ∈ lays, l.home = h0 + i → ∀ kc, l.key = some kc → pst.cache.any (·.key == kc) = true
  | _, [], _, i, H, hH => by simp at hH
  | h0, H0 :: Hs, h, i, H, hH => by
    unfold homesPosRK at h
    obtain ⟨⟨ks, ns, pst⟩, hr, h⟩ := exceptBind_ok h
    dsimp only at h
    split at h
    · next hall =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hH
        subst hH
        refine ⟨ks, ns, pst, hr, fun l hl hlh kc hk => ?_⟩
        have := List.all_eq_true.mp hall l hl
        rw [hk] at this
        simp only [Nat.add_zero] at hlh
        simpa [hlh] using this
      | succ i =>
        simp only [List.getElem?_cons_succ] at hH
        obtain ⟨ks', ns', pst', hr', hall'⟩ := homesPosRK_ok h i H hH
        exact ⟨ks', ns', pst', hr', fun l hl hlh kc hk =>
          hall' l hl (by rw [hlh]; omega) kc hk⟩
    · obtain ⟨_, h, _⟩ := exceptBind_ok h
      exact absurd h throwRK_ne_ok

end Loop

end ConLeche

namespace ConLeche

/-! ## The whole route -/

section Route

/-- The family's majors (`targetNestRouteK`'s `Ms`). -/
@[expose] def nestMsRK (out : List (ConstantVal × TargetMajor × List Expr)) : List TargetMajor :=
  out.map (·.2.1)

/-- The hot flags, per class (`targetNestRouteK`'s `hs`). -/
@[expose] def nestHotRK (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) :
    List Bool :=
  (List.range (nestMsRK out).length).map
    (hotRK (targetGraphOf p) (sccRK (targetGraphOf p)) (nestMsRK out))

/-- The family's shared data as the route builds it. -/
@[expose] def nestFamRK (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) :
    TargetFamily :=
  { recNames := p.recs.map (·.cvR.name),
    rlvls := (p.recs.head?.map fun rc => rc.cvR.levelParams.map Level.param).getD [],
    recTys := out.map (·.1.type), mIs := p.recs.map (·.mI), rPs := p.recs.map (·.rP),
    ranks := some (graphRank (targetGraphOf p)), majors := nestMsRK out }

/-- **The nested route, as run** — at a family with a hot class: the canonical parameter
variables, every recursor's calls, and the final state, where the invariant holds
(`GoodRK`), every pair has been processed, every hot class is paired, and the key-named
positivity check ran on every home. -/
structure NestRouteRun (ops : CheckerOps CheckM) (fe : FEnv) (p : BlockShape)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × TargetMajor × List Expr)) : Type where
  pc : List Expr
  hpc : ∃ (cv0 : ConstantVal) (r : Expr), out.head?.map (·.1) = some cv0 ∧
    openPisAtFvars p.nP cv0.type 0 = some (pc, r)
  calls : List (List CallRK)
  hcalls : (out.zip p.recs).mapM (fun ((cvRi, M, rhss), rc) =>
    recCallsRK ops fe p (cvTas.map ConstantVal.type) (nestFamRK p out) cvRi rc.rP M 0 M.ctors rhss)
      = .ok calls
  st : RouteRK
  good : GoodRK ops fe.env fe p cvTas ctorsAs (nestMsRK out) pc (graphRank (targetGraphOf p))
    (nestHotRK p out) calls st
  done : st.pairs[st.next]? = none
  cover : ∀ c, c < out.length → (nestHotRK p out).getD c false = true →
    ∃ q ∈ st.pairs, q.cls = c
  pos : ∀ (h : Nat) (H : HomeRK), st.homes[h]? = some H → ∃ ks ns pst,
    nestBlockCtorsGoK ops fe.env H.ctx H.holes H.ctors {} = .ok (ks, ns, pst) ∧
    ∀ l ∈ st.lays.toList, l.home = h → ∀ kc, l.key = some kc → pst.cache.any (·.key == kc) = true

/-- **Every pair of the final state has been processed.** -/
theorem NestRouteRun.allDone {ops : CheckerOps CheckM} {fe : FEnv} {p : BlockShape}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : NestRouteRun ops fe p cvTas ctorsAs out) {q : PairRK} (hq : q ∈ R.st.pairs) :
    DoneRK ops fe.env (nestMsRK out) R.pc (graphRank (targetGraphOf p)) (nestHotRK p out)
      R.calls R.st q := by
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hq
  refine R.good.2.2.2.1 k ?_ _ (Array.getElem?_eq_getElem hk)
  apply Classical.byContradiction
  intro hlt
  have hdone := R.done
  have : R.st.next < R.st.pairs.size := by omega
  rw [Array.getElem?_eq_getElem this] at hdone
  exact absurd hdone (by simp)

/-- The empty state satisfies the invariant. -/
theorem goodRK_empty {ops : CheckerOps CheckM} {env : Env} {fe : FEnv} {p : BlockShape}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {Ms : List TargetMajor} {pc : List Expr} {rk : List Nat} {hsF : List Bool}
    {calls : List (List CallRK)} :
    GoodRK ops env fe p cvTas ctorsAs Ms pc rk hsF calls {} := by
  refine ⟨⟨rfl, fun h H hH => by simp at hH⟩, fun i l hl => by simp at hl,
    fun q hq => by simp at hq, fun k hk => by simp at hk, by simp,
    fun ni li σ hn => by simp at hn⟩

set_option maxHeartbeats 4000000 in
/-- **THE inversion of the nested route**: no hot class, or a run record. -/
theorem targetNestRouteK_run {ops : CheckerOps CheckM} {fe : FEnv} {p : BlockShape}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (h : targetNestRouteK (ShadowOps.ofOps ops) fe p cvTas ctorsAs out = .ok ()) :
    (nestHotRK p out).any id = false ∨ Nonempty (NestRouteRun ops fe p cvTas ctorsAs out) := by
  unfold targetNestRouteK at h
  dsimp only at h
  by_cases hhot : (nestHotRK p out).any id = true
  · right
    rw [if_neg (by unfold nestHotRK nestMsRK at hhot; simp only [Bool.not_eq_true']; simpa using hhot)] at h
    simp only [ShadowOps.ofOps] at h
    obtain ⟨cv0, hcv0, h⟩ := exceptBind_ok h
    obtain ⟨⟨pc, r⟩, hpq, h⟩ := exceptBind_ok h
    obtain ⟨calls, hcalls, h⟩ := exceptBind_ok h
    obtain ⟨st1, h1, h⟩ := exceptBind_ok h
    obtain ⟨st2, h2, h⟩ := exceptBind_ok h
    obtain ⟨st3, h3, h⟩ := exceptBind_ok h
    obtain ⟨st4, h4, h⟩ := exceptBind_ok h
    split at h
    · next hcov =>
      obtain ⟨_, hpos, -⟩ := exceptBind_ok h
      obtain ⟨g1, -, -⟩ := seedsRK_ok (rk := graphRank (targetGraphOf p))
        (hsF := nestHotRK p out) (calls := calls) goodRK_empty h1
      obtain ⟨g2, -, -, -, -, -⟩ := routeLoopRK_ok g1 h2
      obtain ⟨g3, -, -⟩ := seedsRK_ok g2 h3
      obtain ⟨g4, -, -, -, -, hnone⟩ := routeLoopRK_ok g3 h4
      refine ⟨{ pc := pc, hpc := ⟨cv0, r, unwrapOrRK_ok hcv0, unwrapOrRK_ok hpq⟩, calls := calls,
                hcalls := hcalls, st := st4, good := g4, done := hnone, cover := ?_,
                pos := fun h H hH => by
                  obtain ⟨ks, ns, pst, hr, hall⟩ :=
                    homesPosRK_ok hpos h H (by rw [Array.getElem?_toList]; exact hH)
                  exact ⟨ks, ns, pst, hr, fun l hl hlh kc hk => hall l hl (by omega) kc hk⟩ }⟩
      intro c hc hh
      have := List.all_eq_true.mp hcov c (List.mem_range.mpr (by simpa using hc))
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
      rcases this with h' | h'
      · exact absurd hh (by unfold nestHotRK nestMsRK; rw [h']; simp)
      · obtain ⟨i, hi, hqc⟩ := Array.any_eq_true.mp h'
        exact ⟨st4.pairs[i], Array.getElem_mem hi, by simpa using hqc⟩
    · exact absurd h throwRK_ne_ok
  · left; simpa using hhot

end Route

end ConLeche
