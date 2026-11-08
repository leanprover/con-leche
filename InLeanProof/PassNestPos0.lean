module

public import InLeanProof.PassNestKey
-- `Expr.hasLooseBVars`'s body (the loose-variable test of a container's parameters)
import all Lean.Expr

/-!
# O7-positivity: the walk's records and its pure steps, read (task #451, lane O7-positivity)

The positivity walk (`nestPos` and its callees) threads a `NestState` and
reads a frame stack of `NestHole`s; InLean's carry `Lean.Expr`s, master's
their readings.  This file fixes the readings and proves the walk's pure
steps master's on them:

* the records: `trKind`, `trHole`, `trNf`, `trSt` (keys and the active list
  through `trKey`, the normal forms through `trNf`, at a state), with their
  side conditions (`KeyOk`, `StOk`), stable as the table grows;
* key comparison (`keyBeq_tr`: InLean's derived `==` is the checker's
  `clEq` on the parameters, so it is equality of readings), membership
  (`contains_trKey`), `nestAcceptGroup`;
* the walk's context against master's (`WalkRel`), the frame stack's holes
  (`rootHoles_tr`, `nestHoleAt_tr`);
* the environment's containers (`nestCtorEntry_tr`, `nestContainer_tr`,
  `nestBlockOf_tr`, `nestFrameMates_tr`).
-/

public section

namespace InLeanProof

open Lean InLean ConLeche.Cached

/-! ## The records -/

/-- A field kind, read. -/
@[expose] def trNK : InLean.NestFieldKind → ConLeche.NestFieldKind
  | .ordinary => .ordinary
  | .recursive t => .recursive t
  | .reflexive t => .reflexive t
  | .inProgress => .inProgress
  | .nested r => .nested r

theorem trNK_ne_ordinary (k : InLean.NestFieldKind) :
    (trNK k != .ordinary) = (k != .ordinary) := by
  cases k <;> rfl

/-- A hole of the frame stack, read at a state. -/
@[expose] def trHole (s : InLean.CState) (h : InLean.NestHole) : ConLeche.NestHole :=
  ⟨trKey s h.key, h.base, h.nIdx⟩

/-- A recorded constructor normal form, read at a state. -/
@[expose] def trNf (s : InLean.CState) (n : InLean.NestCtorNf) : ConLeche.NestCtorNf :=
  ⟨toName n.ctor, n.lvls.map trL, TrSL s n.ds, TrS s n.ty⟩

/-- The walk's state, read at a state. -/
@[expose] def trSt (s : InLean.CState) (st : InLean.NestState) : ConLeche.NestState :=
  ⟨st.keys.map (trKey s), st.active.map (trKey s), st.ctorNfs.map (trNf s)⟩

/-- A key has a reading: its levels and parameters, the parameters closed. -/
@[expose] def KeyOk (s : InLean.CState) (k : InLean.NestKey) : Prop :=
  k.lvls.all okLv = true ∧ OkSL s k.ds = true ∧
    ∀ a ∈ k.ds, (TrS s a).looseBVarsBounded 0 = true

/-- A normal form has a reading. -/
@[expose] def NfOk (s : InLean.CState) (n : InLean.NestCtorNf) : Prop :=
  n.lvls.all okLv = true ∧ OkSL s n.ds = true ∧ OkS s n.ty = true

/-- Every key, active key and normal form of a state has a reading. -/
@[expose] def StOk (s : InLean.CState) (st : InLean.NestState) : Prop :=
  (∀ k ∈ st.keys.toList, KeyOk s k) ∧ (∀ k ∈ st.active, KeyOk s k) ∧
    ∀ n ∈ st.ctorNfs.toList, NfOk s n

theorem closed_of_tabLe {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {l : List Lean.Expr}
    (hok : OkSL s₀ l = true) (hc : ∀ a ∈ l, (TrS s₀ a).looseBVarsBounded 0 = true) :
    ∀ a ∈ l, (TrS s₁ a).looseBVarsBounded 0 = true := by
  intro a ha
  rw [TrS_of_tabLe h (by simp only [OkSL, List.all_eq_true] at hok; exact hok a ha)]
  exact hc a ha

theorem KeyOk.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {k : InLean.NestKey}
    (hk : KeyOk s₀ k) : KeyOk s₁ k ∧ trKey s₁ k = trKey s₀ k := by
  obtain ⟨h1, h2, h3⟩ := hk
  refine ⟨⟨h1, okSL_of_tabLe h h2, closed_of_tabLe h h2 h3⟩, ?_⟩
  simp only [trKey, TrSL_of_tabLe h h2]

theorem NfOk.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {n : InLean.NestCtorNf}
    (hn : NfOk s₀ n) : NfOk s₁ n ∧ trNf s₁ n = trNf s₀ n := by
  obtain ⟨h1, h2, h3⟩ := hn
  refine ⟨⟨h1, okSL_of_tabLe h h2, okS_of_tabLe h h3⟩, ?_⟩
  simp only [trNf, TrSL_of_tabLe h h2, TrS_of_tabLe h h3]

theorem map_trKey_of_tabLe {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) :
    ∀ {l : List InLean.NestKey}, (∀ k ∈ l, KeyOk s₀ k) → l.map (trKey s₁) = l.map (trKey s₀)
  | [], _ => rfl
  | k :: l, hl => by
    simp only [List.map_cons, (KeyOk.mono h (hl k List.mem_cons_self)).2,
      map_trKey_of_tabLe h (fun x hx => hl x (List.mem_cons_of_mem _ hx))]

theorem map_trNf_of_tabLe {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) :
    ∀ {l : List InLean.NestCtorNf}, (∀ n ∈ l, NfOk s₀ n) → l.map (trNf s₁) = l.map (trNf s₀)
  | [], _ => rfl
  | n :: l, hl => by
    simp only [List.map_cons, (NfOk.mono h (hl n List.mem_cons_self)).2,
      map_trNf_of_tabLe h (fun x hx => hl x (List.mem_cons_of_mem _ hx))]

theorem StOk.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {st : InLean.NestState}
    (hst : StOk s₀ st) : StOk s₁ st ∧ trSt s₁ st = trSt s₀ st := by
  obtain ⟨h1, h2, h3⟩ := hst
  refine ⟨⟨fun k hk => (KeyOk.mono h (h1 k hk)).1, fun k hk => (KeyOk.mono h (h2 k hk)).1,
    fun n hn => (NfOk.mono h (h3 n hn)).1⟩, ?_⟩
  have e1 : st.keys.map (trKey s₁) = st.keys.map (trKey s₀) := by
    apply Array.toList_inj.1
    simp only [Array.toList_map]
    exact map_trKey_of_tabLe h h1
  have e3 : st.ctorNfs.map (trNf s₁) = st.ctorNfs.map (trNf s₀) := by
    apply Array.toList_inj.1
    simp only [Array.toList_map]
    exact map_trNf_of_tabLe h h3
  simp only [trSt, e1, e3, map_trKey_of_tabLe h h2]

/-! ## Comparing keys -/

theorem nameBeq_tr (a b : Lean.Name) : (a == b) = (toName a == toName b) := by
  by_cases h : a = b
  · subst h; simp
  · have h' : toName a ≠ toName b := fun he => h (toName_inj he)
    rw [beq_eq_false_iff_ne.2 h, beq_eq_false_iff_ne.2 h']

theorem levelBeq_tr {a b : Lean.Level} (ha : okLv a = true) (hb : okLv b = true) :
    (a == b) = (trL a == trL b) := by
  by_cases h : a = b
  · subst h; simp
  · have h' : trL a ≠ trL b := fun he => h (trL_inj (by simp only [okLv, Bool.and_eq_true] at ha; exact ha.1)
      (by simp only [okLv, Bool.and_eq_true] at hb; exact hb.1) he)
    rw [beq_eq_false_iff_ne.2 h, beq_eq_false_iff_ne.2 h']

theorem levelsBeq_tr : ∀ {l₁ l₂ : List Lean.Level}, l₁.all okLv = true → l₂.all okLv = true →
    (l₁ == l₂) = (l₁.map trL == l₂.map trL)
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | a :: l₁, b :: l₂, h₁, h₂ => by
    simp only [List.all_cons, Bool.and_eq_true] at h₁ h₂
    rw [List.cons_beq_cons, List.map_cons, List.map_cons, List.cons_beq_cons, levelsBeq_tr h₁.2 h₂.2,
      levelBeq_tr h₁.1 h₂.1]

/-- InLean's comparison of parameter lists (the checker's `clEq`) is equality
of readings. -/
theorem exprsBeq_tr {s : InLean.CState} (hfv : FVTableOK s) :
    ∀ {l₁ l₂ : List Lean.Expr}, OkSL s l₁ = true → OkSL s l₂ = true →
      (l₁ == l₂) = (TrSL s l₁ == TrSL s l₂)
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | a :: l₁, b :: l₂, h₁, h₂ => by
    simp only [OkSL_cons, Bool.and_eq_true] at h₁ h₂
    rw [List.cons_beq_cons, TrSL_cons, TrSL_cons, List.cons_beq_cons, exprsBeq_tr hfv h₁.2 h₂.2]
    congr 1
    have hc := clEq_iff_TransS hfv (b := b) (RangeOk_of_OkS h₁.1) (RangeOk_of_OkS h₂.1)
      (TransS_of_ok h₁.1)
    show Expr.clEq a b = _
    by_cases h : TrS s a = TrS s b
    · rw [h] at hc
      simp only [h, beq_self_eq_true]
      exact hc.2 (TransS_of_ok h₂.1)
    · have : Expr.clEq a b = false := by
        cases hab : Expr.clEq a b
        · rfl
        · exact absurd (by have := hc.1 hab; rw [TransS_of_ok h₂.1] at this; exact (Option.some.inj this).symm) h
      simp [this, h]

/-- **Keys compare as their readings.** -/
theorem keyBeq_tr {s : InLean.CState} (hfv : FVTableOK s) {a b : InLean.NestKey}
    (ha : KeyOk s a) (hb : KeyOk s b) : (a == b) = (trKey s a == trKey s b) := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  show InLean.instBEqNestKey.beq _ _ = _
  rw [InLean.instBEqNestKey.beq.eq_1, nameBeq_tr, levelsBeq_tr ha.1 hb.1, exprsBeq_tr hfv ha.2.1 hb.2.1]
  simp only [trKey]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, ConLeche.NestKey.mk.injEq]

/-! ## Membership and the accepted keys -/

theorem contains_trKey_list {s : InLean.CState} (hfv : FVTableOK s) {k : InLean.NestKey}
    (hk : KeyOk s k) :
    ∀ {l : List InLean.NestKey}, (∀ x ∈ l, KeyOk s x) →
      (l.map (trKey s)).contains (trKey s k) = l.contains k
  | [], _ => rfl
  | x :: l, hl => by
    rw [List.map_cons, List.contains_cons, List.contains_cons,
      contains_trKey_list hfv hk (fun y hy => hl y (List.mem_cons_of_mem _ hy)),
      keyBeq_tr hfv hk (hl x List.mem_cons_self)]

/-- **Membership of keys**, read. -/
theorem contains_trKey {s : InLean.CState} (hfv : FVTableOK s) {k : InLean.NestKey}
    (hk : KeyOk s k) {xs : Array InLean.NestKey} (hl : ∀ x ∈ xs.toList, KeyOk s x) :
    (xs.map (trKey s)).contains (trKey s k) = xs.contains k := by
  rw [← Array.contains_toList, ← Array.contains_toList, Array.toList_map]
  exact contains_trKey_list hfv hk hl

/-- A frame's group, read: its members' names and their holes' types. -/
@[expose] def trGrp (s : InLean.CState) (grp : List (Lean.Name × Lean.Expr)) :
    List (ConLeche.Name × ConLeche.Expr) :=
  grp.map fun p => (toName p.1, TrS s p.2)

theorem trGrp_cons (s : InLean.CState) (c : Lean.Name) (ty : Lean.Expr)
    (grp : List (Lean.Name × Lean.Expr)) :
    trGrp s ((c, ty) :: grp) = (toName c, TrS s ty) :: trGrp s grp := rfl

theorem trGrp_append (s : InLean.CState) (g₁ g₂ : List (Lean.Name × Lean.Expr)) :
    trGrp s (g₁ ++ g₂) = trGrp s g₁ ++ trGrp s g₂ := by
  simp [trGrp]

/-- **A frame's group accepted** (`nestAcceptGroup`), read. -/
theorem nestAcceptGroup_tr {s : InLean.CState} (hfv : FVTableOK s) {us : List Lean.Level}
    {ds : List Lean.Expr} (hus : us.all okLv = true) (hds : OkSL s ds = true)
    (hcl : ∀ a ∈ ds, (TrS s a).looseBVarsBounded 0 = true) :
    ∀ (grp : List (Lean.Name × Lean.Expr)) (keys : Array InLean.NestKey),
      (∀ x ∈ keys.toList, KeyOk s x) →
      (∀ x ∈ (InLean.nestAcceptGroup us ds grp keys).toList, KeyOk s x) ∧
      ConLeche.nestAcceptGroup (us.map trL) (TrSL s ds) (trGrp s grp) (keys.map (trKey s)) =
        (InLean.nestAcceptGroup us ds grp keys).map (trKey s)
  | [], keys, hk => ⟨hk, rfl⟩
  | (c, ty) :: rest, keys, hk => by
    have hck : KeyOk s ⟨c, us, ds⟩ := ⟨hus, hds, hcl⟩
    have htr : (⟨toName c, us.map trL, TrSL s ds⟩ : ConLeche.NestKey) = trKey s ⟨c, us, ds⟩ := rfl
    rw [trGrp_cons]
    simp only [InLean.nestAcceptGroup, ConLeche.nestAcceptGroup]
    rw [htr, contains_trKey hfv hck hk]
    by_cases hc : keys.contains ⟨c, us, ds⟩ = true
    · simp only [hc, ↓reduceIte]
      exact nestAcceptGroup_tr hfv hus hds hcl rest keys hk
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [← Array.map_push]
      refine nestAcceptGroup_tr hfv hus hds hcl rest (keys.push _) ?_
      intro x hx
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hk x hx
      · exact hck

/-! ## The walk's context -/

/-- **The walk's context against master's**: what the walk reads of it — the
canonical part (`CanonRel`), the lookup (InLean's environment, master's
`find?` at the relation's environment), the sort, the index counts, and the
canonical parameters through the state. -/
structure WalkRel (fe : InLean.FEnv) (L : ConLeche.Env) (s : InLean.CState)
    (ctx : InLean.NestCtx) (cctx : ConLeche.NestCtx) : Prop where
  canon : CanonRel ctx cctx
  fe : ctx.fe = fe
  find : cctx.find? = L.find?
  sort : cctx.sort = trL ctx.sort
  sortOk : okL ctx.sort = true
  nIdxs : cctx.nIdxs = ctx.nIdxs
  params : cctx.params = TrSL s ctx.params
  paramsOk : OkSL s ctx.params = true
  paramsCl : ∀ a ∈ ctx.params, (TrS s a).looseBVarsBounded 0 = true

theorem WalkRel.mono {fe : InLean.FEnv} {L : ConLeche.Env} {s₀ s₁ : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hW : WalkRel fe L s₀ ctx cctx)
    (h : TabLe s₀ s₁) : WalkRel fe L s₁ ctx cctx where
  canon := hW.canon
  fe := hW.fe
  find := hW.find
  sort := hW.sort
  sortOk := hW.sortOk
  nIdxs := hW.nIdxs
  params := by rw [TrSL_of_tabLe h hW.paramsOk]; exact hW.params
  paramsOk := okSL_of_tabLe h hW.paramsOk
  paramsCl := closed_of_tabLe h hW.paramsOk hW.paramsCl

theorem rootHoles_tr {fe : InLean.FEnv} {L : ConLeche.Env} {s : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hW : WalkRel fe L s ctx cctx) :
    cctx.rootHoles = ctx.rootHoles.map (trHole s) := by
  apply List.ext_getElem
  · simp [ConLeche.NestCtx.rootHoles, InLean.NestCtx.rootHoles, hW.canon.names]
  · intro i h1 h2
    simp only [ConLeche.NestCtx.rootHoles, InLean.NestCtx.rootHoles, List.getElem_mapIdx,
      List.getElem_map, hW.canon.names, hW.canon.lps, hW.canon.nP, hW.params, hW.nIdxs, trHole,
      trKey, params_trL]

/-- **The hole at a depth** (`nestHoleAt`), read. -/
theorem nestHoleAt_tr {fe : InLean.FEnv} {L : ConLeche.Env} {s : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hW : WalkRel fe L s ctx cctx)
    (prog : List InLean.NestHole) (i : Nat) :
    ConLeche.nestHoleAt cctx (prog.map (trHole s)) i =
      (InLean.nestHoleAt ctx prog i).map (trHole s) := by
  unfold ConLeche.nestHoleAt InLean.nestHoleAt
  rw [hW.canon.nP, rootHoles_tr hW]
  split
  · rw [← List.map_reverse, ← List.map_append, List.getElem?_map]
  · rfl

/-! ## The environment's containers -/

theorem nestCtorEntry_tr (C : Lean.Name) (cv : Lean.ConstantVal) (nPc nF : Nat) :
    ConLeche.nestCtorEntry (toName C) (.ctorInfo (trCV cv) nPc nF) =
      (InLean.nestCtorEntry C cv nPc nF).map fun e => (trCV e.1, e.2) := by
  unfold ConLeche.nestCtorEntry InLean.nestCtorEntry
  simp only [trCV_type, stripPis_tr]
  cases InLean.stripPis (nPc + nF) cv.type with
  | none => rfl
  | some p =>
    obtain ⟨ds, body⟩ := p
    simp only [Option.map_some, getAppFn_tr]
    have hs := getAppFnT_shape body
    generalize Expr.getAppFnT body = x at hs
    cases x with
    | const n us =>
      simp only [trC, trE, ← nameBeq_tr]
      split <;> rfl
    | mdata m b => exact (hs.1 m b rfl).elim
    | app f a => exact (hs.2 f a rfl).elim
    | fvar id => rfl
    | _ => rfl

/-- A container's constructor list, read. -/
@[expose] def trCtorL (cs : List (Lean.ConstantVal × Nat)) : List (ConLeche.ConstantVal × Nat) :=
  cs.map fun c => (trCV c.1, c.2)

theorem trCtorL_append (a b : List (Lean.ConstantVal × Nat)) :
    trCtorL (a ++ b) = trCtorL a ++ trCtorL b := by
  simp [trCtorL]

theorem ctorEntry_lookup_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (C n : Lean.Name) :
    (L.find? (toName n)).bind (ConLeche.nestCtorEntry (toName C)) =
      ((fe.ctorView? n).bind fun (cv, nPc, nF) => InLean.nestCtorEntry C cv nPc nF).map
        fun e => (trCV e.1, e.2) := by
  cases hv : fe.ctorView? n with
  | some p =>
    obtain ⟨cv, nP, nF⟩ := p
    obtain ⟨ccv, hcv, hL⟩ := ctorView_rel hJ.pres hv
    rw [hL, hcv.eq_trCV]
    simp only [Option.bind_some]
    exact nestCtorEntry_tr C cv nP nF
  | none =>
    have hn := ctorView_none hJ.pres hv
    simp only [Option.bind_none, Option.map_none]
    cases hL : L.find? (toName n) with
    | none => rfl
    | some ci =>
      cases ci with
      | ctorInfo ccv nP nF => exact (hn ccv nP nF hL).elim
      | _ => rfl

/-- **A container's constructors** (`nestContainer`), read. -/
theorem nestContainer_tr {fe : InLean.FEnv} {L : ConLeche.Env} {s : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L)
    (hW : WalkRel fe L s ctx cctx) (C : Lean.Name) :
    ConLeche.nestContainer cctx (toName C) =
      (InLean.nestContainer ctx C).map fun q => (q.1, trCtorL q.2) := by
  unfold ConLeche.nestContainer InLean.nestContainer
  rw [hW.find, hW.fe]
  cases hv : fe.indView? C with
  | none =>
    have hn := indView_none_tr hJ hv
    cases hL : L.find? (toName C) with
    | none => rfl
    | some ci =>
      cases ci with
      | indInfo ccv caps => exact (hn _ _ hL).elim
      | _ => rfl
  | some p =>
    obtain ⟨cv, caps⟩ := p
    obtain ⟨hL, -, -⟩ := indView_trCV hJ hv
    rw [hL]
    simp only
    have hcs : (toCaps caps).ctors.filterMap
        (fun n => (L.find? n).bind (ConLeche.nestCtorEntry (toName C))) =
        (caps.ctors.filterMap fun n =>
          (fe.ctorView? n).bind fun (cv, nPc, nF) => InLean.nestCtorEntry C cv nPc nF).map
            (fun e => (trCV e.1, e.2)) := by
      simp only [toCaps, List.filterMap_map, List.map_filterMap]
      congr 1
      funext n
      exact ctorEntry_lookup_tr hJ C n
    rw [hcs]
    generalize caps.ctors.filterMap (fun n =>
      (fe.ctorView? n).bind fun (cv, nPc, nF) => InLean.nestCtorEntry C cv nPc nF) = l
    cases l with
    | nil => simp [toCaps, trCtorL]
    | cons x l =>
      obtain ⟨cv0, nPc, nF⟩ := x
      simp [trCtorL]

theorem nestBlockOf_tr {fe : InLean.FEnv} {L : ConLeche.Env} {s : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L)
    (hW : WalkRel fe L s ctx cctx) (C : Lean.Name) :
    ConLeche.nestBlockOf cctx (toName C) = (InLean.nestBlockOf ctx C).map toName := by
  unfold ConLeche.nestBlockOf InLean.nestBlockOf
  rw [hW.find, hW.fe]
  cases hv : fe.indView? C with
  | none =>
    have hn := indView_none_tr hJ hv
    split
    · rename_i hL
      exact (hn _ _ hL).elim
    · rfl
  | some p =>
    obtain ⟨cv, caps⟩ := p
    obtain ⟨hL, -, -⟩ := indView_trCV hJ hv
    rw [hL]
    rfl

theorem eraseDups_map_toName : ∀ (l : List Lean.Name),
    (l.map toName).eraseDups = l.eraseDups.map toName := by
  intro l
  induction h : l.length using Nat.strongRecOn generalizing l with
  | ind n ih =>
    cases l with
    | nil => rfl
    | cons a l =>
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons, List.map_cons, List.filter_map]
      have hf : ((fun b => !b == toName a) ∘ toName) = fun b => !b == a := by
        funext b; simp only [Function.comp, ← nameBeq_tr]
      have hlt : (l.filter fun b => !b == a).length < n := by
        have := List.length_filter_le (fun b => !b == a) l
        simp only [List.length_cons] at h
        omega
      rw [hf, ih _ hlt _ rfl]

/-- **A frame's group-mates** (`nestFrameMates`), read. -/
theorem nestFrameMates_tr {fe : InLean.FEnv} {L : ConLeche.Env} {s : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L)
    (hW : WalkRel fe L s ctx cctx) (C : Lean.Name) :
    ConLeche.nestFrameMates cctx (toName C) = (InLean.nestFrameMates ctx C).map toName := by
  unfold ConLeche.nestFrameMates InLean.nestFrameMates
  rw [nestBlockOf_tr hJ hW, eraseDups_map_toName, List.filter_map]
  congr 2
  funext b
  simp only [Function.comp, bne, ← nameBeq_tr]

/-! ## Replacing variables -/

/-- What the variable replacement needs of a pair of maps: InLean's images
have a reading, which is master's image. -/
@[expose] def FSub (s : InLean.CState) (fI : Nat → Option Lean.Expr)
    (fC : Nat → Option ConLeche.Expr) : Prop :=
  ∀ i, (fI i).map (TrS s) = fC i ∧ ∀ y, fI i = some y → OkS s y = true

/-- The callback of InLean's `replaceFVars`. -/
@[expose] def rfF (fI : Nat → Option Lean.Expr) (x : Lean.Expr) : Option Lean.Expr :=
  match x with
  | .fvar id => match EO.fvDepth? id with
    | some i => fI i
    | none => none
  | x => if x.hasFVar then none else some x

theorem replaceFVars_eq (fI : Nat → Option Lean.Expr) (e : Lean.Expr) :
    InLean.replaceFVars fI e = if !e.hasFVar then e else mapSpec (fun x _ => rfF fI x) e 0 := by
  unfold InLean.replaceFVars EO.replace
  rw [mapOff_spec]; rfl

theorem cReplaceFVars_closed (f : Nat → Option ConLeche.Expr) :
    ∀ (e : ConLeche.Expr), e.hasFvar = false → ConLeche.Expr.replaceFVars f e = e
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar _ _, h => by simp [ConLeche.Expr.hasFvar] at h
  | .app a b, h | .lam a b, h | .forallE a b, h => by
    simp only [ConLeche.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [ConLeche.Expr.replaceFVars, cReplaceFVars_closed f a h.1, cReplaceFVars_closed f b h.2]
  | .letE a b c, h => by
    simp only [ConLeche.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [ConLeche.Expr.replaceFVars, cReplaceFVars_closed f a h.1.1,
      cReplaceFVars_closed f b h.1.2, cReplaceFVars_closed f c h.2]
  | .proj _ _ a, h => by
    simp only [ConLeche.Expr.hasFvar] at h
    simp only [ConLeche.Expr.replaceFVars, cReplaceFVars_closed f a h]

/-- The closed case of the replacement: the node is kept. -/
theorem rf_closed {s : InLean.CState} {fI : Nat → Option Lean.Expr}
    (fC : Nat → Option ConLeche.Expr) {e : Lean.Expr} (k : Nat) (h : OkS s e = true)
    (hc : e.hasFVar = false) (hF : rfF fI e = some e) :
    OkS s (mapSpec (fun x _ => rfF fI x) e k) = true ∧
      TrS s (mapSpec (fun x _ => rfF fI x) e k) = ConLeche.Expr.replaceFVars fC (TrS s e) := by
  rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) hF]
  refine ⟨h, ?_⟩
  rw [cReplaceFVars_closed fC _ (by rw [← hasFVar_TrS s h]; exact hc)]

/-- **InLean's variable replacement, read**: master's on the reading, given
related maps. -/
theorem replaceFVarsI_mapSpec {s : InLean.CState} {fI fC} (hF : FSub s fI fC) :
    ∀ (e : Lean.Expr) (k : Nat), OkS s e = true →
      OkS s (mapSpec (fun x _ => rfF fI x) e k) = true ∧
        TrS s (mapSpec (fun x _ => rfF fI x) e k) = ConLeche.Expr.replaceFVars fC (TrS s e) := by
  intro e
  induction e with
  | fvar id =>
    intro k h
    obtain ⟨d, ty, hT, hd⟩ := TrS_stripTop_fvar (x := .fvar id) h rfl
    rw [hT]
    have hr : rfF fI (.fvar id) = fI d := by simp only [rfF, hd]
    obtain ⟨h1, h2⟩ := hF d
    cases hfi : fI d with
    | none =>
      rw [hfi] at h1
      simp only [mapSpec, hr, hfi, Option.getD_none, ConLeche.Expr.replaceFVars, ← h1,
        Option.map_none]
      exact ⟨h, hT⟩
    | some y =>
      rw [hfi, Option.map_some] at h1
      rw [mapSpec_eq_of_some (f := fun x _ => rfF fI x) (hr.trans hfi)]
      simp only [ConLeche.Expr.replaceFVars, ← h1, Option.getD_some]
      exact ⟨h2 y hfi, by trivial⟩
  | app f a ihf iha =>
    intro k h
    by_cases hc : (Expr.app f a).hasFVar = true
    · have hr : rfF fI (.app f a) = none := by simp only [rfF, hc, ↓reduceIte]
      simp only [OkS_app, Bool.and_eq_true] at h
      simp only [mapSpec, hr, Option.getD_none, OkS_app, TrS_app, ConLeche.Expr.replaceFVars,
        (ihf k h.1).1, (iha k h.2).1, (ihf k h.1).2, (iha k h.2).2, Bool.and_self, true_and]
    · simp only [Bool.not_eq_true] at hc
      exact rf_closed fC k h hc (by simp only [rfF, hc, Bool.false_eq_true, ↓reduceIte])
  | lam nm t b bi iht ihb =>
    intro k h
    by_cases hc : (Expr.lam nm t b bi).hasFVar = true
    · have hr : rfF fI (.lam nm t b bi) = none := by simp only [rfF, hc, ↓reduceIte]
      simp only [OkS_lam, Bool.and_eq_true] at h
      simp only [mapSpec, hr, Option.getD_none, OkS_lam, TrS_lam, ConLeche.Expr.replaceFVars,
        (iht k h.1).1, (ihb (k + 1) h.2).1, (iht k h.1).2, (ihb (k + 1) h.2).2, Bool.and_self,
        true_and]
    · simp only [Bool.not_eq_true] at hc
      exact rf_closed fC k h hc (by simp only [rfF, hc, Bool.false_eq_true, ↓reduceIte])
  | forallE nm t b bi iht ihb =>
    intro k h
    by_cases hc : (Expr.forallE nm t b bi).hasFVar = true
    · have hr : rfF fI (.forallE nm t b bi) = none := by simp only [rfF, hc, ↓reduceIte]
      simp only [OkS_forallE, Bool.and_eq_true] at h
      simp only [mapSpec, hr, Option.getD_none, OkS_forallE, TrS_forallE,
        ConLeche.Expr.replaceFVars, (iht k h.1).1, (ihb (k + 1) h.2).1, (iht k h.1).2,
        (ihb (k + 1) h.2).2, Bool.and_self, true_and]
    · simp only [Bool.not_eq_true] at hc
      exact rf_closed fC k h hc (by simp only [rfF, hc, Bool.false_eq_true, ↓reduceIte])
  | letE nm t v b nd iht ihv ihb =>
    intro k h
    by_cases hc : (Expr.letE nm t v b nd).hasFVar = true
    · have hr : rfF fI (.letE nm t v b nd) = none := by simp only [rfF, hc, ↓reduceIte]
      simp only [OkS_letE, Bool.and_eq_true] at h
      simp only [mapSpec, hr, Option.getD_none, OkS_letE, TrS_letE, ConLeche.Expr.replaceFVars,
        (iht k h.1.1).1, (ihv k h.1.2).1, (ihb (k + 1) h.2).1, (iht k h.1.1).2, (ihv k h.1.2).2,
        (ihb (k + 1) h.2).2, Bool.and_self, true_and]
    · simp only [Bool.not_eq_true] at hc
      exact rf_closed fC k h hc (by simp only [rfF, hc, Bool.false_eq_true, ↓reduceIte])
  | mdata m x ih =>
    intro k h
    by_cases hc : (Expr.mdata m x).hasFVar = true
    · have hr : rfF fI (.mdata m x) = none := by simp only [rfF, hc, ↓reduceIte]
      rw [OkS_mdata] at h
      simp only [mapSpec, hr, Option.getD_none, OkS_mdata, TrS_mdata]
      exact ih k h
    · simp only [Bool.not_eq_true] at hc
      exact rf_closed fC k h hc (by simp only [rfF, hc, Bool.false_eq_true, ↓reduceIte])
  | proj sn i x ih =>
    intro k h
    by_cases hc : (Expr.proj sn i x).hasFVar = true
    · have hr : rfF fI (.proj sn i x) = none := by simp only [rfF, hc, ↓reduceIte]
      rw [OkS_proj] at h
      simp only [mapSpec, hr, Option.getD_none, OkS_proj, TrS_proj, ConLeche.Expr.replaceFVars,
        (ih k h).1, (ih k h).2, true_and]
    · simp only [Bool.not_eq_true] at hc
      exact rf_closed fC k h hc (by simp only [rfF, hc, Bool.false_eq_true, ↓reduceIte])
  | bvar i =>
    intro k h
    have hc : (Expr.bvar i).hasFVar = false := by rw [hasFVar_TrS s h]; rfl
    exact rf_closed fC k h hc (by simp only [rfF, hc, Bool.false_eq_true, ↓reduceIte])
  | sort u =>
    intro k h
    have hc : (Expr.sort u).hasFVar = false := by rw [hasFVar_TrS s h]; rfl
    exact rf_closed fC k h hc (by simp only [rfF, hc, Bool.false_eq_true, ↓reduceIte])
  | const n us =>
    intro k h
    have hc : (Expr.const n us).hasFVar = false := by rw [hasFVar_TrS s h]; rfl
    exact rf_closed fC k h hc (by simp only [rfF, hc, Bool.false_eq_true, ↓reduceIte])
  | lit l =>
    intro k h
    have hc : (Expr.lit l).hasFVar = false := by rw [hasFVar_TrS s h]; rfl
    exact rf_closed fC k h hc (by simp only [rfF, hc, Bool.false_eq_true, ↓reduceIte])
  | mvar i => intro k h; simp [OkS, okE] at h

theorem replaceFVarsI_tr {s : InLean.CState} {fI fC} (hF : FSub s fI fC) {e : Lean.Expr}
    (h : OkS s e = true) :
    OkS s (InLean.replaceFVars fI e) = true ∧
      TrS s (InLean.replaceFVars fI e) = ConLeche.Expr.replaceFVars fC (TrS s e) := by
  rw [replaceFVars_eq]
  by_cases hc : e.hasFVar = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact replaceFVarsI_mapSpec hF e 0 h
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.not_false, ↓reduceIte]
    exact ⟨h, (cReplaceFVars_closed fC _ (by rw [← hasFVar_TrS s h]; exact hc)).symm⟩

theorem replaceFVarsI_trL {s : InLean.CState} {fI fC} (hF : FSub s fI fC) :
    ∀ {l : List Lean.Expr}, OkSL s l = true →
      OkSL s (l.map (InLean.replaceFVars fI)) = true ∧
        TrSL s (l.map (InLean.replaceFVars fI)) = (TrSL s l).map (ConLeche.Expr.replaceFVars fC)
  | [], _ => ⟨rfl, rfl⟩
  | a :: l, h => by
    simp only [OkSL_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := replaceFVarsI_tr hF h.1
    obtain ⟨h3, h4⟩ := replaceFVarsI_trL hF h.2
    simp only [List.map_cons, OkSL_cons, h1, h3, Bool.and_self, TrSL_cons, h2, h4, true_and]

/-- The key map's images (`nestKeyMap`), read. -/
theorem nestKeyMap_sub {s : InLean.CState} {ds holes : List Lean.Expr} (hds : OkSL s ds = true)
    (hh : OkSL s holes = true) :
    FSub s (InLean.nestKeyMap ds holes) (ConLeche.nestKeyMap (TrSL s ds) (TrSL s holes)) := by
  intro i
  have hget : ∀ {l : List Lean.Expr} {j : Nat} {y : Lean.Expr}, OkSL s l = true → l[j]? = some y →
      OkS s y = true := by
    intro l j y hl hy
    simp only [OkSL, List.all_eq_true] at hl
    exact hl y (List.mem_of_getElem? hy)
  unfold InLean.nestKeyMap ConLeche.nestKeyMap
  simp only [TrSL, List.length_map]
  split
  · exact ⟨by rw [List.getElem?_map], fun y hy => hget hds hy⟩
  · exact ⟨by rw [List.getElem?_map], fun y hy => hget hh hy⟩

/-! ## The holes read back -/

/-- Every hole on a frame stack has a reading. -/
@[expose] def ProgOk (s : InLean.CState) (prog : List InLean.NestHole) : Prop :=
  ∀ h ∈ prog, KeyOk s h.key

theorem ProgOk.mono {s₀ s₁ : InLean.CState} (ht : TabLe s₀ s₁) {prog : List InLean.NestHole}
    (h : ProgOk s₀ prog) : ProgOk s₁ prog ∧ prog.map (trHole s₁) = prog.map (trHole s₀) := by
  refine ⟨fun x hx => (KeyOk.mono ht (h x hx)).1, ?_⟩
  apply List.map_congr_left
  intro x hx
  simp only [trHole, (KeyOk.mono ht (h x hx)).2]

theorem getD_names_tr (l : List Lean.Name) (j : Nat) :
    (l.map toName).getD j .anonymous = toName (l.getD j .anonymous) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

/-- **The holes read back** (`nestHoleImg`): InLean's images are master's on
the readings. -/
theorem nestHoleImg_sub {fe : InLean.FEnv} {L : ConLeche.Env} {s : InLean.CState}
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} (hW : WalkRel fe L s ctx cctx) :
    ∀ (prog : List InLean.NestHole), ProgOk s prog →
      FSub s (InLean.nestHoleImg ctx prog) (ConLeche.nestHoleImg cctx (prog.map (trHole s)))
  | [], _ => by
    intro i
    simp only [InLean.nestHoleImg, List.map_nil, ConLeche.nestHoleImg, hiAt_rel hW.canon,
      hW.canon.nP]
    split
    · refine ⟨?_, ?_⟩
      · simp only [Option.map_some, InLean.mkAppL, TrS_mkAppN, TrS_const, hW.params,
          hW.canon.names, hW.canon.lps, params_trL, getD_names_tr]
      · intro y hy
        simp only [Option.some.injEq] at hy
        subst hy
        simp only [InLean.mkAppL, OkS_mkAppN, OkS_const, params_okLv, hW.paramsOk, Bool.and_self]
    · exact ⟨rfl, fun _ h => nomatch h⟩
  | h :: prog, hp => by
    have hp' : ProgOk s prog := fun x hx => hp x (List.mem_cons_of_mem _ hx)
    have hk := hp h List.mem_cons_self
    have ih := nestHoleImg_sub hW prog hp'
    intro i
    simp only [InLean.nestHoleImg, List.map_cons, ConLeche.nestHoleImg, hiAt_rel hW.canon,
      List.length_map]
    split
    · obtain ⟨hok, htr⟩ := replaceFVarsI_trL ih hk.2.1
      refine ⟨?_, ?_⟩
      · simp only [Option.map_some, InLean.mkAppL, TrS_mkAppN, TrS_const, htr, trHole, trKey]
      · intro y hy
        simp only [Option.some.injEq] at hy
        subst hy
        simp only [InLean.mkAppL, OkS_mkAppN, OkS_const, hk.1, hok, Bool.and_self]
    · exact ih i

/-! ## The variable bound and the loose-variable test -/

theorem foldl_fvarB_le (g : Nat → FVarId → Nat)
    (hg : ∀ acc id D, g acc id ≤ D ↔ acc ≤ D ∧ ∀ d, EO.fvDepth? id = some d → d + 1 ≤ D) :
    ∀ (l : List FVarId) (acc D : Nat),
      l.foldl g acc ≤ D ↔ acc ≤ D ∧ ∀ a ∈ l, ∀ d, EO.fvDepth? a = some d → d + 1 ≤ D
  | [], acc, D => by simp
  | a :: l, acc, D => by
    rw [List.foldl_cons, foldl_fvarB_le g hg l, hg]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem fvarRange_TrS_le {s : InLean.CState} (D : Nat) : ∀ {e : Lean.Expr}, OkS s e = true →
    ((TrS s e).fvarRange ≤ D ↔ ∀ a, OccF a e → ∀ d, EO.fvDepth? a = some d → d + 1 ≤ D) := by
  intro e
  induction e with
  | fvar id =>
    intro h
    obtain ⟨d, ty, hT, hd⟩ := TrS_stripTop_fvar (x := .fvar id) h rfl
    rw [hT]
    simp only [ConLeche.Expr.fvarRange, OccF]
    constructor
    · rintro hle a rfl d' hd'
      rw [hd] at hd'; cases hd'; exact hle
    · intro hall; exact hall id rfl d hd
  | app f a ihf iha =>
    intro h
    simp only [OkS_app, Bool.and_eq_true] at h
    simp only [TrS_app, ConLeche.Expr.fvarRange, Nat.max_le, ihf h.1, iha h.2, OccF]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases hx with hx | hx
      · exact h1 x hx
      · exact h2 x hx
    · intro hall; exact ⟨fun x hx => hall x (.inl hx), fun x hx => hall x (.inr hx)⟩
  | lam _ t b _ iht ihb =>
    intro h
    simp only [OkS_lam, Bool.and_eq_true] at h
    simp only [TrS_lam, ConLeche.Expr.fvarRange, Nat.max_le, iht h.1, ihb h.2, OccF]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases hx with hx | hx
      · exact h1 x hx
      · exact h2 x hx
    · intro hall; exact ⟨fun x hx => hall x (.inl hx), fun x hx => hall x (.inr hx)⟩
  | forallE _ t b _ iht ihb =>
    intro h
    simp only [OkS_forallE, Bool.and_eq_true] at h
    simp only [TrS_forallE, ConLeche.Expr.fvarRange, Nat.max_le, iht h.1, ihb h.2, OccF]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases hx with hx | hx
      · exact h1 x hx
      · exact h2 x hx
    · intro hall; exact ⟨fun x hx => hall x (.inl hx), fun x hx => hall x (.inr hx)⟩
  | letE _ t v b _ iht ihv ihb =>
    intro h
    simp only [OkS_letE, Bool.and_eq_true] at h
    simp only [TrS_letE, ConLeche.Expr.fvarRange, Nat.max_le, iht h.1.1, ihv h.1.2, ihb h.2, OccF]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ x hx
      rcases hx with hx | hx | hx
      · exact h1 x hx
      · exact h2 x hx
      · exact h3 x hx
    · intro hall
      exact ⟨⟨fun x hx => hall x (.inl hx), fun x hx => hall x (.inr (.inl hx))⟩,
        fun x hx => hall x (.inr (.inr hx))⟩
  | mdata _ x ih =>
    intro h
    rw [OkS_mdata] at h
    simp only [TrS_mdata, OccF]
    exact ih h
  | proj _ _ x ih =>
    intro h
    rw [OkS_proj] at h
    simp only [TrS_proj, ConLeche.Expr.fvarRange, OccF]
    exact ih h
  | mvar _ => intro h; simp [OkS, okE] at h
  | bvar _ | sort _ | const _ _ | lit _ => intro _; simp [TrS, trE, ConLeche.Expr.fvarRange, OccF]

/-- **InLean's variable bound, read** (`fvarB`): master's on the reading. -/
theorem fvarB_tr {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) :
    InLean.fvarB e = (TrS s e).fvarB := by
  have key : ∀ D, InLean.fvarB e ≤ D ↔ (TrS s e).fvarB ≤ D := by
    intro D
    rw [ConLeche.Expr.fvarB_eq, fvarRange_TrS_le D h]
    unfold InLean.fvarB
    by_cases hf : e.hasFVar = true
    · simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [← Array.foldl_toList, foldl_fvarB_le _ (by
        intro acc id D
        split
        · rename_i d hd
          simp only [Nat.max_le, hd, Option.some.injEq, forall_eq']
        · rename_i hd
          simp only [hd, reduceCtorEq, false_implies, implies_true, and_true])]
      simp only [Nat.zero_le, true_and]
      constructor
      · intro hall a ha d hd
        exact hall a (Array.mem_toList_iff.2 ((mem_fvarIds (RangeOk_of_OkS h) a).2 ha)) d hd
      · intro hall a ha d hd
        exact hall a ((mem_fvarIds (RangeOk_of_OkS h) a).1 (Array.mem_toList_iff.1 ha)) d hd
    · simp only [Bool.not_eq_true] at hf
      simp only [hf, Bool.not_false, ↓reduceIte, Nat.zero_le, true_iff]
      intro a ha
      rw [Expr.hasFVar_eq (RangeOk_of_OkS h)] at hf
      exact absurd ha (not_occF_of_fvarS hf)
  exact Nat.le_antisymm ((key _).2 (Nat.le_refl _)) ((key _).1 (Nat.le_refl _))

/-- A closed reading has no loose bound variable, on both sides. -/
theorem hasLooseBVars_of_closed {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true)
    (hc : (TrS s e).looseBVarsBounded 0 = true) :
    e.hasLooseBVars = false ∧ (TrS s e).bvarB = 0 := by
  refine ⟨?_, ?_⟩
  · show decide (e.looseBVarRange > 0) = false
    rw [Expr.looseBVarRange_eq (RangeOk_of_OkS h)]
    have := rangeS_le_of_lbb hc
    simp only [decide_eq_false_iff_not]
    omega
  · rw [ConLeche.Expr.bvarB_eq]
    have := ConLeche.Expr.looseBVarsBounded_iff.1 hc
    omega

end InLeanProof
