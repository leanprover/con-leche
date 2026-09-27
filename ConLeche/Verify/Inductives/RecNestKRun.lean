module

public import ConLeche.Kernel.Inductives.RecNestK
import ConLeche.Verify.Inductives.PosDerivKInv
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

theorem RouteLe.refl (st : RouteRK) : RouteLe st st :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
    List.prefix_refl _, List.prefix_refl _⟩

theorem RouteLe.trans {a b c : RouteRK} (h₁ : RouteLe a b) (h₂ : RouteLe b c) : RouteLe a c :=
  ⟨h₁.homes.trans h₂.homes, h₁.homeNames.trans h₂.homeNames, h₁.insts.trans h₂.insts,
    h₁.lays.trans h₂.lays, h₁.pairs.trans h₂.pairs, h₁.spells.trans h₂.spells⟩

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
      List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩, rfl, rfl, rfl, rfl, rfl,
      H, hH, Or.inr ⟨rfl, rfl, rfl⟩⟩

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
        array_prefix_push _ _, List.prefix_refl _, List.prefix_refl _⟩, rfl, rfl, rfl, rfl, rfl,
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
        array_prefix_push _ _, List.prefix_refl _, List.prefix_refl _⟩, rfl, rfl, rfl, rfl, rfl,
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
    st.spells.toList <+: st'.spells.toList

theorem SpellsOnly.le {st st' : RouteRK} (h : SpellsOnly st st') : RouteLe st st' := by
  obtain ⟨h1, h2, h3, h4, h5, -, h6⟩ := h
  exact ⟨by rw [h1]; exact List.prefix_refl _, by rw [h2]; exact List.prefix_refl _,
    by rw [h3]; exact List.prefix_refl _, by rw [h4]; exact List.prefix_refl _,
    by rw [h5]; exact List.prefix_refl _, h6⟩

theorem SpellsOnly.refl (st : RouteRK) : SpellsOnly st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _⟩

theorem spellIdxRK_ok {h : Nat} {K : NestKey} {st st' : RouteRK} {i : Nat}
    (hr : spellIdxRK ops env h K st = .ok (i, st')) : SpellsOnly st st' := by
  unfold spellIdxRK at hr
  split at hr
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm
    exact SpellsOnly.refl _
  · obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok hr).symm
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, array_prefix_push _ _⟩

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

theorem addPairRK_le {Ms : List TargetMajor} {strict : Bool} {q : PairRK} {st st' : RouteRK}
    (hr : addPairRK (m := CheckM) Ms strict q st = .ok st') : RouteLe st st' := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ := addPairRK_ok hr
  refine ⟨by rw [h1]; exact List.prefix_refl _, by rw [h2]; exact List.prefix_refl _,
    by rw [h3]; exact List.prefix_refl _, by rw [h4]; exact List.prefix_refl _, ?_,
    by rw [h6]; exact List.prefix_refl _⟩
  rcases h7 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · rw [h]; exact List.prefix_refl _
  · rw [h]; exact array_prefix_push _ _
  · rw [h]; exact List.prefix_refl _

/-- **The callee's node a leaf names** (`childRK`): the root at a member hole, the
family's key's layout at a family, the same layout at an own hole, the key's layout at a
container key. -/
@[expose] def ChildKindRK (I : InstRK) (q : PairRK) (lay : LayRK) : LeafRK → Nat → LayRK → Prop
  | .mem _, _, lay' => LayKeyRK I.home none lay'
  | .fam j, _, lay' => ∃ kj, (lay.L.fams[j]?).map (·.1) = some kj ∧ LayKeyRK I.home (some kj) lay'
  | .own _, li, _ => li = q.lay
  | .key kc, _, lay' => LayKeyRK I.home (some kc) lay'

/-- **Only the layouts grow.** -/
@[expose] def LaysOnly (st st' : RouteRK) : Prop :=
  st'.homes = st.homes ∧ st'.homeNames = st.homeNames ∧ st'.insts = st.insts ∧
    st'.pairs = st.pairs ∧ st'.next = st.next ∧ st'.spells = st.spells ∧
    st.lays.toList <+: st'.lays.toList

theorem LaysOnly.le {st st' : RouteRK} (h : LaysOnly st st') : RouteLe st st' := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ := h
  exact ⟨by rw [h1]; exact List.prefix_refl _, by rw [h2]; exact List.prefix_refl _,
    by rw [h3]; exact List.prefix_refl _, h7, by rw [h4]; exact List.prefix_refl _,
    by rw [h6]; exact List.prefix_refl _⟩

theorem LaysOnly.refl (st : RouteRK) : LaysOnly st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _⟩

theorem layIdxRK_laysOnly {h : Nat} {key : Option NestKey} {st st' : RouteRK} {i : Nat}
    (hr : layIdxRK ops env h key st = .ok (i, st')) : LaysOnly st st' := by
  obtain ⟨hle, h1, h2, h3, h4, h5, h6, -⟩ := layIdxRK_ok hr
  exact ⟨h1, h6, h2, h3, h4, h5, hle.lays⟩

/-- **The callee's node, as run** (`childRK`). -/
theorem childRK_ok {I : InstRK} {q : PairRK} {lay : LayRK} {kind : LeafRK} {cn : Name}
    {st st' : RouteRK} {li mi : Nat}
    (hr : childRK ops env I q lay kind cn st = .ok (li, mi, st')) :
    LaysOnly st st' ∧ ∃ lay', st'.lays[li]? = some lay' ∧
      lay'.mems.findIdx? (· == cn) = some mi ∧ ChildKindRK I q lay kind li lay' := by
  unfold childRK at hr
  cases kind with
  | mem t =>
    dsimp only at hr
    obtain ⟨⟨li0, st1⟩, h1, hr⟩ := exceptBind_ok hr
    dsimp only at hr
    obtain ⟨lay', hl', hr⟩ := exceptBind_ok hr
    obtain ⟨mi0, hmi, hr⟩ := exceptBind_ok hr
    obtain ⟨rfl, rfl, rfl⟩ : li0 = li ∧ mi0 = mi ∧ st1 = st' := by
      have := pureRK_ok hr; simp only [Prod.mk.injEq] at this; exact ⟨this.1, this.2.1, this.2.2⟩
    have hl'' := unwrapOrRK_ok hl'
    have hmi' := unwrapOrRK_ok hmi
    obtain ⟨l, hl, hk⟩ := layIdxRK_key h1
    rw [hl''] at hl; obtain rfl := Option.some.inj hl
    exact ⟨layIdxRK_laysOnly h1, lay', hl'', hmi', hk⟩
  | fam j =>
    dsimp only at hr
    obtain ⟨kj, hkj, hr⟩ := exceptBind_ok hr
    obtain ⟨⟨li0, st1⟩, h1, hr⟩ := exceptBind_ok hr
    dsimp only at hr
    have hkj' := unwrapOrRK_ok hkj
    obtain ⟨lay', hl', hr⟩ := exceptBind_ok hr
    obtain ⟨mi0, hmi, hr⟩ := exceptBind_ok hr
    obtain ⟨rfl, rfl, rfl⟩ : li0 = li ∧ mi0 = mi ∧ st1 = st' := by
      have := pureRK_ok hr; simp only [Prod.mk.injEq] at this; exact ⟨this.1, this.2.1, this.2.2⟩
    have hl'' := unwrapOrRK_ok hl'
    have hmi' := unwrapOrRK_ok hmi
    obtain ⟨l, hl, hk⟩ := layIdxRK_key h1
    rw [hl''] at hl; obtain rfl := Option.some.inj hl
    exact ⟨layIdxRK_laysOnly h1, lay', hl'', hmi', kj, hkj', hk⟩
  | own g =>
    dsimp only at hr
    obtain ⟨⟨li0, st1⟩, h1, hr⟩ := exceptBind_ok hr
    dsimp only at hr
    obtain ⟨lay', hl', hr⟩ := exceptBind_ok hr
    obtain ⟨mi0, hmi, hr⟩ := exceptBind_ok hr
    obtain ⟨rfl, rfl, rfl⟩ : li0 = li ∧ mi0 = mi ∧ st1 = st' := by
      have := pureRK_ok hr; simp only [Prod.mk.injEq] at this; exact ⟨this.1, this.2.1, this.2.2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pureRK_ok h1)
    have hl'' := unwrapOrRK_ok hl'
    have hmi' := unwrapOrRK_ok hmi
    exact ⟨LaysOnly.refl _, lay', hl'', hmi', rfl⟩
  | key kc =>
    dsimp only at hr
    obtain ⟨⟨li0, st1⟩, h1, hr⟩ := exceptBind_ok hr
    dsimp only at hr
    obtain ⟨lay', hl', hr⟩ := exceptBind_ok hr
    obtain ⟨mi0, hmi, hr⟩ := exceptBind_ok hr
    obtain ⟨rfl, rfl, rfl⟩ : li0 = li ∧ mi0 = mi ∧ st1 = st' := by
      have := pureRK_ok hr; simp only [Prod.mk.injEq] at this; exact ⟨this.1, this.2.1, this.2.2⟩
    have hl'' := unwrapOrRK_ok hl'
    have hmi' := unwrapOrRK_ok hmi
    obtain ⟨l, hl, hk⟩ := layIdxRK_key h1
    rw [hl''] at hl; obtain rfl := Option.some.inj hl
    exact ⟨layIdxRK_laysOnly h1, lay', hl'', hmi', hk⟩

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

theorem childRK_laysOk {I : InstRK} {q : PairRK} {lay : LayRK} {kind : LeafRK} {cn : Name}
    {st st' : RouteRK} {li mi : Nat} (hL : LaysOkRK ops env st)
    (hr : childRK ops env I q lay kind cn st = .ok (li, mi, st')) : LaysOkRK ops env st' := by
  unfold childRK at hr
  cases kind with
  | mem t =>
    dsimp only at hr
    obtain ⟨⟨li0, st1⟩, h1, hr⟩ := exceptBind_ok hr
    dsimp only at hr
    obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    have hp := pureRK_ok hr
    simp only [Prod.mk.injEq] at hp
    obtain ⟨-, -, rfl⟩ := hp
    exact layIdxRK_laysOk hL h1
  | fam j =>
    dsimp only at hr
    obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain ⟨⟨li0, st1⟩, h1, hr⟩ := exceptBind_ok hr
    dsimp only at hr
    obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    have hp := pureRK_ok hr
    simp only [Prod.mk.injEq] at hp
    obtain ⟨-, -, rfl⟩ := hp
    exact layIdxRK_laysOk hL h1
  | own g =>
    dsimp only at hr
    obtain ⟨⟨li0, st1⟩, h1, hr⟩ := exceptBind_ok hr
    dsimp only at hr
    obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    have hp := pureRK_ok hr
    simp only [Prod.mk.injEq] at hp
    obtain ⟨-, -, rfl⟩ := hp
    obtain ⟨-, rfl⟩ := Prod.mk.inj (pureRK_ok h1)
    exact hL
  | key kc =>
    dsimp only at hr
    obtain ⟨⟨li0, st1⟩, h1, hr⟩ := exceptBind_ok hr
    dsimp only at hr
    obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    obtain ⟨_, _, hr⟩ := exceptBind_ok hr
    have hp := pureRK_ok hr
    simp only [Prod.mk.injEq] at hp
    obtain ⟨-, -, rfl⟩ := hp
    exact layIdxRK_laysOk hL h1

end Ops

/-! ## A call's facts -/

section Call

variable (ops : CheckerOps CheckM) (env : Env) (Ms : List TargetMajor) (pc : List Expr)

/-- The canonical renaming of a class's parameters (`callRK`'s `rn`). -/
@[expose] def rnRK (pc : List Expr) (e : Expr) : Expr := e.replaceFVars fun i => pc[i]?

/-- The relocated holes of a call at a pair's layout. -/
@[expose] def hsRK (H : HomeRK) (I : InstRK) (lay : LayRK) (c : CallRK) : List Expr :=
  relocHolesRK H I c.base lay.holeTys []

/-- The head and parameters of the callee's hole application (`callRK`'s `(hd, psR)`). -/
@[expose] def hdRK (H : HomeRK) (lay : LayRK) (hs : List Expr) (M'' : TargetMajor)
    (dsC : List Expr) : LeafRK → Expr × List Expr
  | .mem t => (hs.getD t default, dsC)
  | .fam j => (hs.getD (H.ctx.names.length + j) default, [])
  | .own g => (hs.getD (H.ctx.names.length + lay.L.nF + g) default, dsC)
  | .key _ => (.const M''.ind M''.lvls, dsC)

/-- **The per-component match of a call, as run** at a pair (`matchRK` against the leaf of
the called field's normal form at the pair's node). -/
@[expose] def MatchRunRK (st : RouteRK) (q : PairRK) (c : CallRK) (r : LeafRK × Name × List Expr) :
    Prop :=
  ∃ I H lay nf, st.insts[q.inst]? = some I ∧ st.homes[I.home]? = some H ∧
    st.lays[q.lay]? = some lay ∧
    ((lay.nfs.getD q.mem []).getD c.ctor [])[c.ih.field]? = some nf ∧
    matchRK ops env H I lay (hsRK H I lay c) (famSubstRK H I lay (hsRK H I lay c))
      (c.base + (hsRK H I lay c).length) (rnRK pc) c.cn (Ms.getD c.ih.callee default) nf
      = .ok r

/-- **A strict call's typing, as run**: the node's crest field (holes relocated, at the
rule's field variables) and the callee's hole at its abstracted parameters and the call's
indices, under the call's telescope, both inferred and defeq at the relocated depth. -/
@[expose] def TypingRunRK (st : RouteRK) (q : PairRK) (c : CallRK) (kind : LeafRK)
    (dsC : List Expr) : Prop :=
  ∃ I H lay crest fldH, st.insts[q.inst]? = some I ∧ st.homes[I.home]? = some H ∧
    st.lays[q.lay]? = some lay ∧ (lay.crests.getD q.mem [])[c.ctor]? = some crest ∧
    ((targetPiDomsWith c.fvsF (relocRK H I (hsRK H I lay c) crest)).getD [])[c.ih.field]?
      = some fldH ∧
    (∃ ty, ops.inferType env (c.base + (hsRK H I lay c).length) fldH = .ok ty) ∧
    (∃ ty, ops.inferType env (c.base + (hsRK H I lay c).length)
      (Expr.mkPisOf (c.teles.getD c.ih.field [])
        (Expr.mkAppN (hdRK H lay (hsRK H I lay c) (Ms.getD c.ih.callee default) dsC kind).1
          ((hdRK H lay (hsRK H I lay c) (Ms.getD c.ih.callee default) dsC kind).2 ++ c.ih.idx)))
      = .ok ty) ∧
    ops.isDefEq env (c.base + (hsRK H I lay c).length) fldH
      (Expr.mkPisOf (c.teles.getD c.ih.field [])
        (Expr.mkAppN (hdRK H lay (hsRK H I lay c) (Ms.getD c.ih.callee default) dsC kind).1
          ((hdRK H lay (hsRK H I lay c) (Ms.getD c.ih.callee default) dsC kind).2 ++ c.ih.idx)))
      = .ok true

/-- **The callee's node at a call** (`childRK`): the layout `li` and member `mi` the leaf
names, from the caller pair's instance and layout. -/
@[expose] def CalleeAtRK (st : RouteRK) (q : PairRK) (kind : LeafRK) (cn : Name) (li mi : Nat) :
    Prop :=
  ∃ I lay lay', st.insts[q.inst]? = some I ∧ st.lays[q.lay]? = some lay ∧
    st.lays[li]? = some lay' ∧ lay'.mems.findIdx? (· == cn) = some mi ∧
    ChildKindRK I q lay kind li lay'

/-- **A strict call, as run**: matched, typed, and its callee paired at the node its leaf
names. -/
@[expose] def StrictRunRK (st : RouteRK) (q : PairRK) (c : CallRK) : Prop :=
  ∃ kind cn dsC, MatchRunRK ops env Ms pc st q c (kind, cn, dsC) ∧
    TypingRunRK ops env Ms st q c kind dsC ∧
    ∃ li mi sp, (⟨c.ih.callee, q.inst, li, mi, sp⟩ : PairRK) ∈ st.pairs ∧
      CalleeAtRK st q kind cn li mi

end Call

theorem MatchRunRK.mono {ops : CheckerOps CheckM} {env : Env} {Ms : List TargetMajor}
    {pc : List Expr} {st st' : RouteRK} (hle : RouteLe st st') {q : PairRK} {c : CallRK}
    {r : LeafRK × Name × List Expr} (h : MatchRunRK ops env Ms pc st q c r) :
    MatchRunRK ops env Ms pc st' q c r := by
  obtain ⟨I, H, lay, nf, h1, h2, h3, h4, h5⟩ := h
  exact ⟨I, H, lay, nf, hle.inst h1, hle.home h2, hle.lay h3, h4, h5⟩

theorem TypingRunRK.mono {ops : CheckerOps CheckM} {env : Env} {Ms : List TargetMajor}
    {st st' : RouteRK} (hle : RouteLe st st') {q : PairRK} {c : CallRK} {kind : LeafRK}
    {dsC : List Expr} (h : TypingRunRK ops env Ms st q c kind dsC) :
    TypingRunRK ops env Ms st' q c kind dsC := by
  obtain ⟨I, H, lay, crest, fldH, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨I, H, lay, crest, fldH, hle.inst h1, hle.home h2, hle.lay h3, h4, h5, h6⟩

theorem CalleeAtRK.mono {st st' : RouteRK} (hle : RouteLe st st') {q : PairRK} {kind : LeafRK}
    {cn : Name} {li mi : Nat} (h : CalleeAtRK st q kind cn li mi) : CalleeAtRK st' q kind cn li mi := by
  obtain ⟨I, lay, lay', h1, h2, h3, h4⟩ := h
  exact ⟨I, lay, lay', hle.inst h1, hle.lay h2, hle.lay h3, h4⟩

theorem StrictRunRK.mono {ops : CheckerOps CheckM} {env : Env} {Ms : List TargetMajor}
    {pc : List Expr} {st st' : RouteRK} (hle : RouteLe st st') {q : PairRK} {c : CallRK}
    (h : StrictRunRK ops env Ms pc st q c) : StrictRunRK ops env Ms pc st' q c := by
  obtain ⟨kind, cn, dsC, h1, h2, li, mi, sp, h3, h4⟩ := h
  exact ⟨kind, cn, dsC, h1.mono hle, h2.mono hle, li, mi, sp, hle.pair h3, h4.mono hle⟩

end ConLeche

namespace ConLeche

section CallRun

/-- A soft match that answered: its body succeeded (the handler only answers `none`). -/
theorem tryCatchRK_some {α : Type} {x : CheckM α} {y : α}
    (h : tryCatchThe CheckError (do let a ← x; pure (some a))
      (fun err => match err with
        | .invalid _ => pure none
        | e => throw e) = .ok (some y)) : x = .ok y := by
  rcases tryCatchK_ok h with h | ⟨err, _, h⟩
  · obtain ⟨a, ha, h⟩ := exceptBind_ok h
    obtain rfl : a = y := Option.some.inj (pureRK_ok h)
    exact ha
  · exfalso
    revert h
    split
    · intro h; exact absurd (pureRK_ok h) (by simp)
    · exact throwRK_ne_ok

variable {ops : CheckerOps CheckM} {env : Env} {Ms : List TargetMajor} {pc : List Expr}

/-- What a call adds to the pairs: nothing, or its callee's pair, matched, at the node its
leaf names, with agreeing constructors. -/
@[expose] def CallAddRK (ops : CheckerOps CheckM) (env : Env) (Ms : List TargetMajor)
    (pc : List Expr) (st st' : RouteRK) (q : PairRK) (c : CallRK) : Prop :=
  st'.pairs = st.pairs ∨ ∃ kind cn dsC li mi sp,
    st'.pairs = st.pairs.push ⟨c.ih.callee, q.inst, li, mi, sp⟩ ∧
    MatchRunRK ops env Ms pc st q c (kind, cn, dsC) ∧ CalleeAtRK st' q kind cn li mi ∧
    ∃ lay', st'.lays[li]? = some lay' ∧
      ctorsAgreeRK (Ms.getD c.ih.callee default).ctors (lay'.ctors.getD mi []) = true

/-- The strict arm of `callRK`, from its steps' runs. -/
theorem callStrict_fin {st st1 st2 st' : RouteRK} {q : PairRK} {c : CallRK} {I : InstRK}
    {H : HomeRK} {lay : LayRK} {kind : LeafRK} {cn : Name} {dsC : List Expr} {crest fldH : Expr}
    {li mi sp : Nat}
    (hI : st.insts[q.inst]? = some I) (hH : st.homes[I.home]? = some H)
    (hlay : st.lays[q.lay]? = some lay)
    (hmr : MatchRunRK ops env Ms pc st q c (kind, cn, dsC))
    (hcrest : (lay.crests.getD q.mem [])[c.ctor]? = some crest)
    (hfld : ((targetPiDomsWith c.fvsF (relocRK H I (hsRK H I lay c) crest)).getD [])[c.ih.field]?
      = some fldH)
    (h1 : ∃ ty, ops.inferType env (c.base + (hsRK H I lay c).length) fldH = .ok ty)
    (h2 : ∃ ty, ops.inferType env (c.base + (hsRK H I lay c).length)
      (Expr.mkPisOf (c.teles.getD c.ih.field [])
        (Expr.mkAppN (hdRK H lay (hsRK H I lay c) (Ms.getD c.ih.callee default) dsC kind).1
          ((hdRK H lay (hsRK H I lay c) (Ms.getD c.ih.callee default) dsC kind).2 ++ c.ih.idx)))
      = .ok ty)
    (hb : ops.isDefEq env (c.base + (hsRK H I lay c).length) fldH
      (Expr.mkPisOf (c.teles.getD c.ih.field [])
        (Expr.mkAppN (hdRK H lay (hsRK H I lay c) (Ms.getD c.ih.callee default) dsC kind).1
          ((hdRK H lay (hsRK H I lay c) (Ms.getD c.ih.callee default) dsC kind).2 ++ c.ih.idx)))
      = .ok true)
    (hch : childRK ops env I q lay kind cn st = .ok (li, mi, st1))
    (hS2 : SpellsOnly st1 st2)
    (hr : addPairRK (m := CheckM) Ms true ⟨c.ih.callee, q.inst, li, mi, sp⟩ st2 = .ok st') :
    RouteLe st st' ∧ st'.homes = st.homes ∧ st'.homeNames = st.homeNames ∧
      st'.insts = st.insts ∧ st'.next = st.next ∧
      (LaysOkRK ops env st → LaysOkRK ops env st') ∧ CallAddRK ops env Ms pc st st' q c ∧
      (true = true → StrictRunRK ops env Ms pc st' q c) := by
  obtain ⟨hL1, lay'', hl'', hmi, hck⟩ := childRK_ok hch
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := addPairRK_ok hr
  have hle1 := hL1.le
  have hle2 := hS2.le
  have hle3 := addPairRK_le hr
  have hle := hle1.trans (hle2.trans hle3)
  obtain ⟨b1, b2, b3, b4, b5, b6, -⟩ := hL1
  obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := hS2
  have hca : CalleeAtRK st' q kind cn li mi := by
    refine ⟨I, lay, lay'', ?_, hle.lay hlay, ?_, hmi, hck⟩
    · rw [a3, c3, b3]; exact hI
    · rw [a4, c4]; exact hl''
  have hty : TypingRunRK ops env Ms st q c kind dsC :=
    ⟨I, H, lay, crest, fldH, hI, hH, hlay, hcrest, hfld, h1, h2, hb⟩
  refine ⟨hle, by rw [a1, c1, b1], by rw [a2, c2, b2], by rw [a3, c3, b3],
    by rw [a5, c6, b5], fun hL => ?_, ?_, fun _ => ?_⟩
  · have := childRK_laysOk hL hch
    unfold LaysOkRK at this ⊢
    rw [a4, c4, a1, c1]; exact this
  · rcases a7 with ⟨h, -⟩ | ⟨h, lay3, hl3, hag⟩ | ⟨h, -⟩
    · left; rw [h, c5, b4]
    · right
      refine ⟨kind, cn, dsC, li, mi, sp, by rw [h, c5, b4], hmr, hca, lay3, ?_, hag⟩
      rw [a4]; exact hl3
    · exact absurd h (by simp)
  · refine ⟨kind, cn, dsC, hmr.mono hle, hty.mono hle, li, mi, sp, ?_, hca⟩
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
      (strict = true → StrictRunRK ops env Ms pc st' q c) := by
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
    | none =>
      obtain rfl := pureRK_ok hr
      exact ⟨RouteLe.refl _, rfl, rfl, rfl, rfl, id, Or.inl rfl, fun h => nomatch h⟩
    | some x =>
      obtain ⟨kind, cn, dsC0⟩ := x
      have hm := tryCatchRK_some hrr
      dsimp only at hr
      obtain ⟨⟨li, mi, st1⟩, hch, hr⟩ := exceptBind_ok hr
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
      have hca : CalleeAtRK st' q kind cn li mi := by
        refine ⟨I, lay, lay'', ?_, hle.lay hlay, ?_, hmi, hck⟩
        · rw [a3, c3, b3]; exact hI
        · rw [a4, c4]; exact hl''
      refine ⟨hle, by rw [a1, c1, b1], by rw [a2, c2, b2], by rw [a3, c3, b3],
        by rw [a5, c6, b5], fun hL => ?_, ?_, fun h => nomatch h⟩
      · have := childRK_laysOk hL hch
        unfold LaysOkRK at this ⊢
        rw [a4, c4, a1, c1]; exact this
      · rcases a7 with ⟨h, -⟩ | ⟨h, lay3, hl3, hag⟩ | ⟨-, h⟩
        · left; rw [h, c5, b4]
        · right
          refine ⟨kind, cn, dsC0, li, mi, sp, by rw [h, c5, b4], hmr, hca, lay3, ?_, hag⟩
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
    cases kind <;>
    · dsimp only at hr
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
            obtain ⟨⟨li, mi, st1⟩, hch, hr⟩ := exceptBind_ok hr
            obtain ⟨lay', -, hr⟩ := exceptBind_ok hr
            obtain ⟨⟨sp, st2⟩, hcs, hr⟩ := exceptBind_ok hr
            exact callStrict_fin hI hH hlay hmr hcrest hfld ⟨ty1, h1⟩ ⟨ty2, h2⟩ hb hch
              (calleeSpellRK_ok hcs) hr
          · exact absurd hr throwRK_ne_ok
        · exact absurd hr throwRK_ne_ok
      · obtain ⟨_, h, _⟩ := exceptBind_ok hr
        exact absurd h throwRK_ne_ok

/-- **The per-component match, as run** (`matchRK`): the leaf of the field's normal form
at the node, the callee's inductive and levels (`Level.isEquivList`), and the callee's
abstracted parameters pairwise defeq to the leaf's relocated ones, each inferred. -/
theorem matchRK_ok {H : HomeRK} {I : InstRK} {lay : LayRK} {hs : List Expr}
    {S : List (NestKey × Expr)} {d : Nat} {rn : Expr → Expr} {cnR : Name} {M'' : TargetMajor}
    {nf : Expr} {kind : LeafRK} {cn : Name} {dsC : List Expr}
    (h : matchRK ops env H I lay hs S d rn cnR M'' nf = .ok (kind, cn, dsC)) :
    ∃ lvls ps, leafRK H lay nf = some (kind, cn, lvls, ps) ∧ M''.ind = cn ∧
      Level.isEquivList M''.lvls (lvls.map (lvl1RK H I)) = some true ∧
      dsC = M''.ds.map (fun x => absRK H I lay S hs (rn x)) ∧
      paramsDefEqRK ops env d cnR dsC (ps.map fun x => absRK H I lay S hs (relocRK H I hs x))
        = .ok () := by
  unfold matchRK at h
  split at h
  · next kind0 cn0 lvls ps hleaf =>
    dsimp only at h
    by_cases hc : (M''.ind == cn0 &&
        (Level.isEquivList M''.lvls (lvls.map (lvl1RK H I))).getD false) = true
    · rw [if_pos hc] at h
      obtain ⟨_, hpd, h⟩ := exceptBind_ok h
      have hp := pureRK_ok h
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      refine ⟨lvls, ps, hleaf, hc.1, ?_, rfl, hpd⟩
      have hc2 := hc.2
      cases he : Level.isEquivList M''.lvls (List.map (lvl1RK H I) lvls) with
      | none => rw [he] at hc2; simp at hc2
      | some b => rw [he] at hc2; simp at hc2; rw [hc2]
    · rw [if_neg hc] at h
      obtain ⟨_, h, _⟩ := exceptBind_ok h
      exact absurd h throwRK_ne_ok
  · exact absurd h throwRK_ne_ok

end CallRun

/-! ## The pairs' invariant -/

section Inv

variable (ops : CheckerOps CheckM) (env : Env) (fe : FEnv) (p : BlockShape)
  (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
  (Ms : List TargetMajor) (pc : List Expr) (rk : List Nat) (hsF : List Bool)
  (calls : List (List CallRK))

/-- **A pair is valid**: its instance and layout exist, at one home; its member is its
class's inductive, whose constructors agree with the class's. -/
@[expose] def PairValidRK (st : RouteRK) (q : PairRK) : Prop :=
  ∃ I lay, st.insts[q.inst]? = some I ∧ st.lays[q.lay]? = some lay ∧ lay.home = I.home ∧
    lay.mems[q.mem]? = some (Ms.getD q.cls default).ind ∧
    ctorsAgreeRK (Ms.getD q.cls default).ctors (lay.ctors.getD q.mem []) = true

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
        CalleeAtRK st q0 kind cn q.lay q.mem

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
    st.next ≤ st.pairs.size

end Inv

section InvMono

variable {ops : CheckerOps CheckM} {env : Env} {fe : FEnv} {p : BlockShape}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {Ms : List TargetMajor} {pc : List Expr} {rk : List Nat} {hsF : List Bool}
  {calls : List (List CallRK)} {st st' : RouteRK}

theorem PairValidRK.mono (hle : RouteLe st st') {q : PairRK} (h : PairValidRK Ms st q) :
    PairValidRK Ms st' q := by
  obtain ⟨I, lay, h1, h2, h3, h4, h5⟩ := h
  exact ⟨I, lay, hle.inst h1, hle.lay h2, h3, h4, h5⟩

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
    {dsC : List Expr} {li mi sp : Nat} (hq : PairValidRK Ms st q)
    (hm : MatchRunRK ops env Ms pc st q c (kind, cn, dsC)) (hca : CalleeAtRK st q kind cn li mi)
    (hag : ∃ lay', st.lays[li]? = some lay' ∧
      ctorsAgreeRK (Ms.getD c.ih.callee default).ctors (lay'.ctors.getD mi []) = true) :
    PairValidRK Ms st ⟨c.ih.callee, q.inst, li, mi, sp⟩ := by
  obtain ⟨I, lay, hI, hlay, hhome, -, -⟩ := hq
  obtain ⟨I', H, lay0, nf, hI', -, -, -, hmr⟩ := hm
  obtain ⟨I'', lay1, lay', hI'', hlay1, hl', hmi, hck⟩ := hca
  rw [hI] at hI' hI''
  obtain rfl := Option.some.inj hI'
  obtain rfl := Option.some.inj hI''
  rw [hlay] at hlay1
  obtain rfl := Option.some.inj hlay1
  obtain ⟨lvls, ps, -, hcn, -⟩ := matchRK_ok hmr
  obtain ⟨lay2, hl2, hag⟩ := hag
  rw [hl'] at hl2
  obtain rfl := Option.some.inj hl2
  refine ⟨I, lay', hI, hl', ?_, ?_, hag⟩
  · have hkey : ∀ {key : Option NestKey}, LayKeyRK I.home key lay' → lay'.home = I.home := by
      intro key hk
      rcases hk with hp | ⟨hh, -⟩
      · unfold layPredRK at hp
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact hp.1
      · exact hh
    cases kind with
    | mem t => exact hkey hck
    | fam j => obtain ⟨kj, -, hk⟩ := hck; exact hkey hk
    | own g =>
      have hli : li = q.lay := hck
      rw [hli, hlay] at hl'
      obtain rfl := Option.some.inj hl'
      exact hhome
    | key kc => exact hkey hck
  · obtain ⟨hlt, hbeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hmi
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
      ∀ q' ∈ st'.pairs, q' ∈ st.pairs ∨ ∃ c ∈ cs, c.ih.callee = q'.cls ∧ q'.inst = q.inst ∧
        ∃ kind cn dsC, MatchRunRK ops env Ms pc st' q c (kind, cn, dsC) ∧
          CalleeAtRK st' q kind cn q'.lay q'.mem ∧ ∃ lay', st'.lays[q'.lay]? = some lay' ∧
            ctorsAgreeRK (Ms.getD q'.cls default).ctors (lay'.ctors.getD q'.mem []) = true
  | [], st, st', h => by
    unfold pairCallsRK at h
    obtain rfl := pureRK_ok h
    exact ⟨RouteLe.refl _, rfl, rfl, rfl, rfl, id, fun _ h => (nomatch h), fun q' h => Or.inl h⟩
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
    obtain ⟨le2, e1, e2, e3, e4, lays2, strict2, new2⟩ := pairCallsRK_ok h
    -- the head call
    have head : RouteLe st st1 ∧ st1.homes = st.homes ∧ st1.homeNames = st.homeNames ∧
        st1.insts = st.insts ∧ st1.next = st.next ∧
        (LaysOkRK ops env st → LaysOkRK ops env st1) ∧ CallAddRK ops env Ms pc st st1 q c ∧
        ((rk.getD c.ih.callee 0 == rk.getD q.cls 0) = true → hsF.getD q.cls false = true →
          StrictRunRK ops env Ms pc st1 q c) := by
      split at h1
      · next hskip =>
        obtain rfl := pureRK_ok h1
        refine ⟨RouteLe.refl _, rfl, rfl, rfl, rfl, id, Or.inl rfl, fun h1 h2 => ?_⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hskip
        rw [hskip.2] at h2; exact absurd h2 (by simp)
      · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := callRK_ok h1
        exact ⟨a1, a2, a3, a4, a5, a6, a7, fun hi _ => a8 hi⟩
    obtain ⟨le1, d1, d2, d3, d4, lays1, add1, strict1⟩ := head
    refine ⟨le1.trans le2, by rw [e1, d1], by rw [e2, d2], by rw [e3, d3], by rw [e4, d4],
      fun hL => lays2 (lays1 hL), ?_, ?_⟩
    · intro c' hc' hi hh
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact (strict1 hi hh).mono le2
      · exact strict2 c' hc' hi hh
    · intro q' hq'
      rcases new2 q' hq' with hq1 | ⟨c', hc', rest⟩
      · rcases add1 with hsame | ⟨kind, cn, dsC, li, mi, sp, hpush, hm, hca, lay', hl', hag⟩
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
      obtain ⟨hHo, hLo, hPo, hDo, hNx⟩ := hG
      have hqm : q ∈ st.pairs := Array.mem_of_getElem? hq
      obtain ⟨le2, e1, e2, e3, e4, lays2, strict2, new2⟩ := pairCallsRK_ok h2
      have le1 : RouteLe st { st with next := st.next + 1 } :=
        ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
          List.prefix_refl _, List.prefix_refl _⟩
      have le := le1.trans le2
      have hG2 : GoodRK ops env fe p cvTas ctorsAs Ms pc rk hsF calls st2 := by
        refine ⟨?_, lays2 hLo, ?_, ?_, ?_⟩
        · unfold HomesOkRK at hHo ⊢
          rw [e1, e2]; exact hHo
        · intro q' hq'
          rcases new2 q' hq' with hq1 | ⟨c, hc, hcal, hins, kind, cn, dsC, hm, hca, lay', hl', hag⟩
          · obtain ⟨hv, ho⟩ := hPo q' hq1
            exact ⟨hv.mono le, ho.mono le⟩
          · obtain ⟨cls, inst, li, mi, sp⟩ := q'
            simp only at hcal hins hca hl' hag
            subst hcal hins
            have hvq := (hPo q hqm).1.mono le
            exact ⟨pairValid_callee hvq hm hca ⟨lay', hl', hag⟩,
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
    (ei : st1.insts.toList <+: st2.insts.toList)
    (hI : st2.insts[ii]? = some I) (hIh : I.home = hh) (hIus : I.us = (Ms.getD c default).lvls)
    (hIds : I.ds.map Expr.eraseFVarTys =
      ((Ms.getD c default).ds.map (rnRK pc)).map Expr.eraseFVarTys)
    (h3 : layIdxRK ops fe.env hh none st2 = .ok (li, st3))
    (hH : st3.homes[hh]? = some H)
    (ht : H.ctx.names.findIdx? (· == (Ms.getD c default).ind) = some t)
    (h4 : addPairRK (m := CheckM) Ms true ⟨c, ii, li, t, 0⟩ st3 = .ok st4) :
    GoodRK ops fe.env fe p cvTas ctorsAs Ms pc rk hsF calls st4 ∧ RouteLe st1 st4 ∧
      st4.next = st1.next := by
  obtain ⟨hHo, hLo, hPo, hDo, hNx⟩ := hG1
  have le12 : RouteLe st1 st2 :=
    ⟨by rw [e1]; exact List.prefix_refl _, by rw [e2]; exact List.prefix_refl _, ei,
      by rw [e3]; exact List.prefix_refl _, by rw [e4]; exact List.prefix_refl _,
      by rw [e6]; exact List.prefix_refl _⟩
  obtain ⟨le3, f1, f2, f3, f4, f5, f6, -⟩ := layIdxRK_ok h3
  obtain ⟨lay, hlay, hkey⟩ := layIdxRK_key h3
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := addPairRK_ok h4
  have le4 := addPairRK_le h4
  have le := le12.trans (le3.trans le4)
  have hL2 : LaysOkRK ops fe.env st2 := by
    unfold LaysOkRK at hLo ⊢; rw [e3, e1]; exact hLo
  have hL3 := layIdxRK_laysOk hL2 h3
  -- the new pair's layout is its home's root
  have hlay4 : st4.lays[li]? = some lay := by rw [a4]; exact hlay
  have hroot : lay.home = hh ∧ lay.key = none ∧ lay.mems = H.ctx.names := by
    obtain ⟨H', hH', hk⟩ := hL3 li lay hlay
    have hlh : lay.home = hh := by
      rcases hkey with hp | ⟨hh', -⟩
      · unfold layPredRK at hp; simp only [Bool.and_eq_true, beq_iff_eq] at hp; exact hp.1
      · exact hh'
    rw [hlh, hH] at hH'
    obtain rfl := Option.some.inj hH'
    rcases hk with ⟨hk0, hr0⟩ | ⟨kc, hk0, -⟩
    · exact ⟨hlh, hk0, rootLayRK_mems hr0⟩
    · exfalso
      rcases hkey with hp | ⟨-, hk'⟩
      · unfold layPredRK at hp; rw [hk0] at hp; simp at hp
      · rw [hk0] at hk'; exact absurd hk' (by simp)
  obtain ⟨hlh, hlk, hlm⟩ := hroot
  have hH1 : st1.homes[hh]? = some H := by rw [← e1, ← f1]; exact hH
  obtain ⟨H', hH', hHn⟩ := hname H hH1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, le, by rw [a5, f4, e5]⟩
  · unfold HomesOkRK at hHo ⊢; rw [a1, a2, f1, f6, e1, e2]; exact hHo
  · unfold LaysOkRK at hL3 ⊢; rw [a4, a1]; exact hL3
  · intro q hq
    have hold : q ∈ st3.pairs → PairValidRK Ms st4 q ∧
        OriginRK ops fe.env fe p cvTas ctorsAs Ms pc calls st4 q := by
      intro hq3
      rw [f3, e4] at hq3
      obtain ⟨hv, ho⟩ := hPo q hq3
      exact ⟨hv.mono (le12.trans (le3.trans le4)), ho.mono (le12.trans (le3.trans le4))⟩
    rcases a7 with ⟨h, -⟩ | ⟨h, lay', hl', hag⟩ | ⟨h, -⟩
    · exact hold (by rw [← h]; exact hq)
    · rw [h] at hq
      rcases Array.mem_push.mp hq with hq | rfl
      · exact hold hq
      · rw [hlay] at hl'
        obtain rfl := Option.some.inj hl'
        have hI4 : st4.insts[ii]? = some I := by rw [a3, f2]; exact hI
        refine ⟨⟨I, lay, hI4, hlay4, by rw [hlh, hIh], ?_, hag⟩, Or.inl ?_⟩
        · obtain ⟨hlt, hbeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp ht
          simp only [beq_iff_eq] at hbeq
          rw [hlm, List.getElem?_eq_getElem hlt, hbeq]
        · refine ⟨I, H, lay, hI4, ?_, hlay4, hlk, hIus, hIds, H', hH', hHn⟩
          rw [a1, hIh]; exact hH
    · exact absurd h (by simp)
  · intro k hk q hq
    rw [a5, f4, e5] at hk
    obtain ⟨q1, hq1⟩ : ∃ q1, st1.pairs[k]? = some q1 :=
      ⟨st1.pairs[k]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
    have := le.pairAt hq1
    rw [hq] at this
    obtain rfl := Option.some.inj this
    exact (hDo k hk q hq1).mono le
  · have h2 := le.pairs.length_le
    simp only [Array.length_toList] at h2
    rw [a5, f4, e5]; omega

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
    obtain ⟨hHo, hLo, hPo, hDo, hNx⟩ := hG
    obtain ⟨hHo1, -⟩ := homeIdxRK_homesOk hHo h1
    have hname : ∀ H1, st1.homes[hh]? = some H1 → ∃ H', homeRK (m := CheckM) fe p cvTas
        ctorsAs (Ms.getD c default) = .ok H' ∧ H'.ctx.names = H1.ctx.names := by
      intro H1 hH1
      obtain ⟨-, H, hH, H', hH', hn⟩ := homeIdxRK_homesOk hHo h1
      rw [hH] at hH1; obtain rfl := Option.some.inj hH1
      exact ⟨H', hH', hn⟩
    have hG1 : GoodRK ops fe.env fe p cvTas ctorsAs Ms pc rk hsF calls st1 := by
      refine ⟨hHo1, laysOkRK_homes hLo le1.homes l1, fun q hq => ?_, fun k hk q hq => ?_, ?_⟩
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
      obtain ⟨hG4, le4, n4⟩ := seedStep_good hG1 hname rfl rfl rfl rfl rfl rfl
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
        hG1 hname rfl rfl rfl rfl rfl rfl
        (array_prefix_push _ _) Array.getElem?_push_size rfl rfl rfl h3 (unwrapOrRK_ok hH)
        (unwrapOrRK_ok ht) h4
      obtain ⟨hG', le', n'⟩ := seedsRK_ok hG4 h
      exact ⟨hG', le1.trans (le4.trans le'), by rw [n', n4, n1]⟩

/-- The positivity re-run on the homes (`homesPosRK`), per home. -/
theorem homesPosRK_ok {env : Env} :
    ∀ {Hs : List HomeRK}, homesPosRK ops env Hs = .ok () →
      ∀ H ∈ Hs, ∃ r, nestBlockCtorsK ops env H.ctx H.holes H.ctors = .ok r
  | [], _, _, hH => nomatch hH
  | H0 :: Hs, h, H, hH => by
    unfold homesPosRK at h
    obtain ⟨r, hr, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hH with rfl | hH
    · exact ⟨r, hr⟩
    · exact homesPosRK_ok h H hH

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
  pos : ∀ H ∈ st.homes.toList, ∃ r, nestBlockCtorsK ops fe.env H.ctx H.holes H.ctors = .ok r

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
    fun q hq => by simp at hq, fun k hk => by simp at hk, by simp⟩

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
                pos := homesPosRK_ok hpos }⟩
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
