module

public import ConLeche.Verify.Inductives.PosCompleteFrame

public section

/-!
# The elimination link (lane COMPLETE-4, (A))

Official's `elimNested` (`OfficialNested.lean`) replaces nested
occurrences with a GROWING auxiliary map, one constructor at a time, and
reads "mentions a type of the declaration" over the GROWING list of its
types.  The completeness proof reads the result against the FINAL map,
over the members only (`sigmaAll`).  This module relates the two:

* on a term free of auxiliary names (every term official replaces is: a
  replaced occurrence is not descended into), official's
  `isNestedApp` over its type list agrees with the one over the members
  (`isNestedApp_congr`);
* `sigmaAll` is stable under extending the map (`sigmaAll_compat`);
* `replaceAll` from a state computes `sigmaAll` against every map that
  extends the one it ends with (`replaceAll_spec`).
-/

namespace ConLeche

open Expr

section Elim

variable {c : Official.ElimCtx}

/-! ## Occurrences off the auxiliary names -/

theorem nestOcc_congr_noAux {G : Name → Bool} {mem mem' : List Name}
    (h : ∀ n, G n = false → mem.contains n = mem'.contains n) :
    ∀ (x : Expr), NoAux G x → x.nestOcc mem 0 0 = x.nestOcc mem' 0 0 := by
  intro x
  induction x with
  | const n us => intro hx; simp only [NoAux] at hx; simp only [Expr.nestOcc, h n hx]
  | app f a ihf iha => intro hx; simp only [NoAux] at hx; simp only [Expr.nestOcc, ihf hx.1, iha hx.2]
  | lam t b m iht ihb => intro hx; simp only [NoAux] at hx; simp only [Expr.nestOcc, iht hx.1, ihb hx.2]
  | forallE t b m iht ihb =>
    intro hx; simp only [NoAux] at hx; simp only [Expr.nestOcc, iht hx.1, ihb hx.2]
  | letE t v b iht ihv ihb =>
    intro hx; simp only [NoAux] at hx
    simp only [Expr.nestOcc, iht hx.1, ihv hx.2.1, ihb hx.2.2]
  | proj s i x ih => intro hx; simp only [NoAux] at hx; simp only [Expr.nestOcc, ih hx]
  | _ => intro _; rfl

theorem noAux_getAppArgs {G : Name → Bool} : ∀ (e : Expr), NoAux G e → ∀ x ∈ e.getAppArgs, NoAux G x := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h x hx
    simp only [NoAux] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ihf h.1 x hx
    · exact h.2
  | _ => intro _ x hx; simp [Expr.getAppArgs] at hx

theorem noAux_getAppFn {G : Name → Bool} : ∀ (e : Expr), NoAux G e → NoAux G e.getAppFn := by
  intro e
  induction e with
  | app f a ihf _ => intro h; simp only [NoAux] at h; simpa [Expr.getAppFn] using ihf h.1
  | _ => intro h; simpa [Expr.getAppFn] using h

theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.any_cons]
    rw [h y List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **Official's nested-occurrence test off the auxiliary names**: on a
term free of them, it reads the same over any two lists of declared
names that agree off them. -/
theorem isNestedApp_congr {G : Name → Bool} {mem mem' : List Name}
    (h : ∀ n, G n = false → mem.contains n = mem'.contains n) {e : Expr} (he : NoAux G e) :
    Official.isNestedApp c mem e = Official.isNestedApp c mem' e := by
  have hargs := noAux_getAppArgs e he
  cases e with
  | app f a =>
    simp only [Official.isNestedApp]
    split
    · split
      · rename_i caps _
        rw [any_congr_mem (l := ((Expr.app f a).getAppArgs.take caps.nparams))
          (fun x hx => nestOcc_congr_noAux h x (hargs x (List.mem_of_mem_take hx)))]
      · rfl
    · rfl
  | _ => rfl

/-! ## `sigmaAll` against a growing map -/

/-- `M` extends `A` as a lookup table. -/
@[expose] def Compat (A M : List (Expr × Name)) : Prop :=
  ∀ k x, A.lookup k = some x → M.lookup k = some x

theorem Compat.refl (A : List (Expr × Name)) : Compat A A := fun _ _ h => h

theorem Compat.trans {A B C : List (Expr × Name)} (h₁ : Compat A B) (h₂ : Compat B C) :
    Compat A C := fun k x h => h₂ k x (h₁ k x h)

theorem Compat.append (A B : List (Expr × Name)) : Compat A (A ++ B) := by
  intro k x h
  induction A with
  | nil => simp at h
  | cons p A ih =>
    obtain ⟨k', x'⟩ := p
    by_cases hk : (k == k') = true
    · simp only [List.lookup, List.cons_append, hk] at h ⊢; exact h
    · simp only [Bool.not_eq_true] at hk
      simp only [List.lookup, List.cons_append, hk] at h ⊢
      exact ih h

/-- **`sigmaAll` is stable under extending the map.** -/
theorem sigmaAll_compat {mem : List Name} {A M : List (Expr × Name)} (hAM : Compat A M) :
    ∀ (e : Expr), SigOk c mem A e → SigOk c mem M e ∧ sigmaAll c mem M e = sigmaAll c mem A e := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro h
    rcases hN : Official.isNestedApp c mem (.app f a) with err | (_ | ⟨I, us, np, args⟩)
    · simp only [SigOk, hN] at h
    · simp only [SigOk, hN] at h
      obtain ⟨hf', ef⟩ := ihf h.1
      obtain ⟨ha', ea⟩ := iha h.2
      simp only [SigOk, sigmaAll, hN, ef, ea]
      exact ⟨⟨hf', ha'⟩, trivial⟩
    · simp only [SigOk, hN] at h
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
      simp only [SigOk, sigmaAll, hN, hAM _ _ hx, hx, Option.isSome_some, and_self]
  | lam t b m iht ihb =>
    intro h; simp only [SigOk] at h
    obtain ⟨h1, e1⟩ := iht h.1; obtain ⟨h2, e2⟩ := ihb h.2
    exact ⟨⟨h1, h2⟩, by simp only [sigmaAll, e1, e2]⟩
  | forallE t b m iht ihb =>
    intro h; simp only [SigOk] at h
    obtain ⟨h1, e1⟩ := iht h.1; obtain ⟨h2, e2⟩ := ihb h.2
    exact ⟨⟨h1, h2⟩, by simp only [sigmaAll, e1, e2]⟩
  | letE t v b iht ihv ihb =>
    intro h; simp only [SigOk] at h
    obtain ⟨h1, e1⟩ := iht h.1; obtain ⟨h2, e2⟩ := ihv h.2.1; obtain ⟨h3, e3⟩ := ihb h.2.2
    exact ⟨⟨h1, h2, h3⟩, by simp only [sigmaAll, e1, e2, e3]⟩
  | proj s i x ih =>
    intro h; simp only [SigOk] at h
    obtain ⟨h1, e1⟩ := ih h
    exact ⟨h1, by simp only [sigmaAll, e1]⟩
  | _ => intro h; exact ⟨h, rfl⟩

end Elim

/-! ## The elimination's operational specs (lane COMPLETE-5) -/

namespace Official

theorem instPiParams_ok {e : Expr} {args : List Expr} {r : Expr} :
    instPiParams e args = .ok r ↔ instPisWith args e = some r := by
  unfold instPiParams; split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem mapM_except_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {rs : List β}, l.mapM f = .ok rs → ∀ a ∈ l, ∃ r ∈ rs, f a = .ok r
  | [], rs, h, a, ha => by simp at ha
  | a :: l, rs, h, b, hb => by
    rw [List.mapM_cons] at h
    rcases ha : f a with e | r
    · simp [ha, bind, Except.bind] at h
    · rcases hl : l.mapM f with e | rs'
      · simp [ha, hl, bind, Except.bind] at h
      · simp [ha, hl, bind, Except.bind, pure, Except.pure] at h
        subst h
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨r, List.mem_cons_self, ha⟩
        · obtain ⟨r', hr', h'⟩ := mapM_except_mem hl b hb
          exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem mapM_except_mem' {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {rs : List β}, l.mapM f = .ok rs → ∀ r ∈ rs, ∃ a ∈ l, f a = .ok r
  | [], rs, h, r, hr => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; simp at hr
  | a :: l, rs, h, b, hb => by
    rw [List.mapM_cons] at h
    rcases ha : f a with e | r
    · simp [ha, bind, Except.bind] at h
    · rcases hl : l.mapM f with e | rs'
      · simp [ha, hl, bind, Except.bind] at h
      · simp [ha, hl, bind, Except.bind, pure, Except.pure] at h
        subst h
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨r', hr', h'⟩ := mapM_except_mem' hl b hb
          exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem mapM_except_det {α β ε : Type} {f : α → Except ε β} {l : List α} {rs rs' : List β}
    (h : l.mapM f = .ok rs) (h' : l.mapM f = .ok rs') : rs = rs' := by
  rw [h] at h'; cases h'; rfl

theorem mapM_lift_run {σ α β ε : Type} (f : α → Except ε β) (s : σ) :
    ∀ (l : List α), (l.mapM (fun x => (monadLift (f x) : StateT σ (Except ε) β))).run s =
      (l.mapM f).map (fun r => (r, s))
  | [] => by simp [List.mapM_nil]; rfl
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons]
    simp only [StateT.run_bind, StateT.run_monadLift]
    rcases ha : f a with e | r
    · simp [bind, Except.bind, Except.map]
    · have := mapM_lift_run f s l
      simp only [bind, Except.bind, Except.map] at this ⊢
      have hm : (monadLift (Except.ok r : Except ε β) : Except ε β) = .ok r := rfl
      rw [hm]
      simp only [pure, Except.pure]
      rw [this]
      rcases hl : List.mapM f l with e | rs <;> rfl


/-- One auxiliary type as `copyBlock` makes it from the container `J` at
`us`/`ds`: its former and its RAW constructors (still mentioning the
containers). -/
@[expose] def CopyOk (c : ElimCtx) (us : List Level) (ds : List Expr) (J : Name) (t : AuxType) : Prop :=
  ∃ cv caps, c.find? J = some (.indInfo cv caps) ∧
    instPiParams (cv.type.instantiateLevelParams cv.levelParams us) ds = .ok t.type ∧
    (c.ctorsOf J).mapM (fun x => instPiParams (x.1.type.instantiateLevelParams x.1.levelParams us) ds)
      = .ok t.ctors

/-- **`copyBlock`'s spec**: the block's types appended, in order, each
under a fresh name and keyed by `J Ds`. -/
theorem copyBlock_spec {c : ElimCtx} {us : List Level} {ds : List Expr} :
    ∀ (Js : List Name) (s s' : ElimSt), (copyBlock c us ds Js).run s = .ok ((), s') →
      s'.next = s.next + Js.length ∧
      s'.aux = s.aux ++ Js.mapIdx (fun j J => (Expr.mkAppN (.const J us) ds, c.auxName (s.next + j))) ∧
      ∃ ts : List AuxType, s'.types.toList = s.types.toList ++ ts ∧ ts.length = Js.length ∧
        ∀ j (hj : j < Js.length), ∃ t, ts[j]? = some t ∧ t.name = c.auxName (s.next + j) ∧
          CopyOk c us ds Js[j] t
  | [], s, s', h => by
    simp only [copyBlock, pure] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨by simp, by simp, [], by simp, rfl, fun j hj => by simp at hj⟩
  | J :: Js, s, s', h => by
    simp only [copyBlock] at h
    split at h
    next cv caps hf =>
      simp only [pure_bind, StateT.run_bind, StateT.run_get, liftM, StateT.run_monadLift,
        StateT.run_set, bind_assoc, pure_bind] at h
      rcases hty : instPiParams (instantiateLevelParams cv.levelParams us cv.type) ds with e | ty
      · simp [hty, bind, Except.bind] at h
      rw [mapM_lift_run] at h
      rcases hcs : (c.ctorsOf J).mapM
          (fun x => instPiParams (x.1.type.instantiateLevelParams x.1.levelParams us) ds) with e | cs
      · simp [hty, hcs, bind, Except.bind, Except.map] at h
      simp only [hty, hcs, bind, Except.bind, Except.map] at h
      have hm : (monadLift (Except.ok ty : Except CheckError Expr) : Except CheckError Expr) =
        .ok ty := rfl
      rw [hm] at h
      obtain ⟨hn, ha, ts, hts, hlen, hj⟩ := copyBlock_spec Js _ _ h
      refine ⟨by simp only [hn, List.length_cons]; omega, ?_, ⟨c.auxName s.next, ty, cs⟩ :: ts, ?_, ?_, ?_⟩
      · rw [ha]
        simp only [List.mapIdx_cons, List.append_assoc, List.singleton_append, Nat.add_zero]
        congr 3
        funext j J'
        congr 2
        omega
      · rw [hts]; simp
      · simp [hlen]
      · intro j hjl
        cases j with
        | zero => exact ⟨_, rfl, by simp, cv, caps, hf, hty, hcs⟩
        | succ j =>
          obtain ⟨t, ht, hn', hc⟩ := hj j (by simpa using hjl)
          exact ⟨t, by simpa using ht, by rw [hn']; show c.auxName (s.next + 1 + j) = _; congr 1; omega, by simpa using hc⟩
    next hnf =>
      simp only [StateT.run_bind, liftM, StateT.run_monadLift] at h
      have : (throw illFormed : ElimM ConstantVal).run s = .error illFormed := rfl
      simp [this, bind, Except.bind] at h


/-- **`isNestedApp`'s positive answer**, unfolded. -/
theorem isNestedApp_some {c : ElimCtx} {names : List Name} {e : Expr} {I : Name} {us : List Level}
    {np : Nat} {args : List Expr} (h : isNestedApp c names e = .ok (some (I, us, np, args))) :
    e.getAppFn = .const I us ∧ args = e.getAppArgs ∧ I ≠ quotName ∧
      ∃ cv caps, c.find? I = some (.indInfo cv caps) ∧ np = caps.nparams ∧ np ≤ args.length ∧
        (args.take np).any (·.nestOcc names 0 0) = true ∧ ∀ x ∈ args.take np, x.bvarB = 0 := by
  unfold isNestedApp at h
  split at h
  next f a =>
    split at h
    next I' us' hfn =>
      split at h
      next cv caps hf =>
        by_cases hq : (I' == quotName) = true
        · simp [hq, pure, Except.pure] at h
        simp only [hq, if_false, Bool.false_eq_true] at h
        by_cases hl : (Expr.app f a).getAppArgs.length < caps.nparams
        · simp [hl, pure, Except.pure] at h
        simp only [hl, if_false] at h
        by_cases ho : ((Expr.app f a).getAppArgs.take caps.nparams).any (·.nestOcc names 0 0) = true
        · simp only [ho, Bool.not_true, Bool.false_eq_true, if_false] at h
          by_cases hb : ((Expr.app f a).getAppArgs.take caps.nparams).any (·.bvarB != 0) = true
          · simp [hb, throw, throwThe, MonadExceptOf.throw] at h
          simp only [hb, if_false, Bool.false_eq_true, pure, Except.pure, Except.ok.injEq,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          refine ⟨hfn, rfl, by simpa using hq, cv, caps, hf, rfl, by omega, ho, fun x hx => ?_⟩
          simp only [List.any_eq_true, bne_iff_ne, ne_eq, not_exists, not_and] at hb
          simpa using hb x hx
        · simp [ho, pure, Except.pure] at h
      next => simp [pure, Except.pure] at h
    next => simp [pure, Except.pure] at h
  next => simp [pure, Except.pure] at h

/-- The names of the declaration's types in a state. -/
@[expose] def ElimSt.names (s : ElimSt) : List Name := s.types.toList.map (·.name)

/-- The key of a nested occurrence. -/
@[expose] def keyOf (I : Name) (us : List Level) (np : Nat) (args : List Expr) : Expr :=
  Expr.mkAppN (.const I us) (args.take np)

/-- **`replaceIfNested`'s spec**: no nested occurrence (state unchanged),
or one whose key the map names after the call — found, or added by
copying the head's whole block. -/
theorem replaceIfNested_spec {c : ElimCtx} {e : Expr} {s s' : ElimSt} {r : Option Expr}
    (h : (replaceIfNested c e).run s = .ok (r, s')) :
    (r = none ∧ isNestedApp c s.names e = .ok none ∧ s' = s) ∨
    ∃ I us np args a, r = some (Expr.mkAppN (Expr.mkAppN (.const a c.lvls) c.ps) (args.drop np)) ∧
      isNestedApp c s.names e = .ok (some (I, us, np, args)) ∧
      s'.aux.lookup (keyOf I us np args) = some a ∧
      (s' = s ∨ (copyBlock c us (args.take np) (blockOf c I)).run s = .ok ((), s')) := by
  simp only [replaceIfNested, StateT.run_bind, StateT.run_get, pure_bind, liftM,
    StateT.run_monadLift] at h
  rcases hN : isNestedApp c (s.types.toList.map (·.name)) e with err | (_ | ⟨I, us, np, args⟩)
  · simp [hN, bind, Except.bind] at h
  · simp [hN, bind, Except.bind, pure, Except.pure] at h
    simp only [StateT.run, StateT.pure, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inl ⟨rfl, hN, rfl⟩
  · simp [hN, bind, Except.bind, pure, Except.pure] at h
    refine .inr ⟨I, us, np, args, ?_⟩
    rcases hl : List.lookup ((const I us).mkAppN (List.take np args)) s.aux with _ | a
    · simp only [hl] at h
      simp only [StateT.run, StateT.bind, bind, Except.bind] at h
      rcases hcb : copyBlock c us (List.take np args) (blockOf c I) s with err | ⟨⟨⟩, s1⟩
      · simp [hcb] at h
      simp only [hcb, get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure] at h
      rcases hl' : List.lookup ((const I us).mkAppN (List.take np args)) s1.aux with _ | a
      · simp [hl', throw, throwThe, MonadExceptOf.throw, StateT.lift] at h
        cases h
      · simp only [hl', StateT.pure, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨a, rfl, hN, hl', .inr hcb⟩
    · simp only [hl, StateT.run, StateT.pure, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨a, rfl, hN, hl, .inl rfl⟩

end Official

/-! ## The elimination's invariant -/

section Inv

variable (c : Official.ElimCtx) (mem : List Name) (G : Name → Bool)

theorem noAux_instantiateLevelParams {ks : List Name} {us : List Level} :
    ∀ (e : Expr), NoAux G e → NoAux G (e.instantiateLevelParams ks us) := by
  intro e
  induction e with
  | const n vs => intro h; exact h
  | app f a ihf iha => intro h; exact ⟨ihf h.1, iha h.2⟩
  | lam t b m iht ihb => intro h; exact ⟨iht h.1, ihb h.2⟩
  | forallE t b m iht ihb => intro h; exact ⟨iht h.1, ihb h.2⟩
  | letE t v b iht ihv ihb => intro h; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i x ih => intro h; exact ih h
  | _ => intro _; trivial

/-- A nested occurrence's key, as official records it: `I` a stored
inductive (not `Quot`) at its parameter count, the parameters closed, free
of auxiliary names and mentioning a member. -/
@[expose] def KeyPre (I : Name) (ds : List Expr) : Prop :=
  (∃ cv caps, c.find? I = some (.indInfo cv caps) ∧ caps.nparams = ds.length) ∧ I ≠ quotName ∧
    (∀ x ∈ ds, x.bvarB = 0 ∧ NoAux G x) ∧ ds.any (·.nestOcc mem 0 0) = true

/-- A type's constructors against its RAW ones: processed (`p`) — replaced
against the map `A` —, or not yet. -/
@[expose] def CtorsOk (p : Prop) (A : List (Expr × Name)) (raws cs : List Expr) : Prop :=
  (∀ u ∈ raws, NoAux G u) ∧ (p → (∀ u ∈ raws, SigOk c mem A u) ∧ cs = raws.map (sigmaAll c mem A)) ∧
    (¬p → cs = raws)

/-- A member's type in the elimination's state. -/
@[expose] def MemTy (p : Prop) (A : List (Expr × Name)) (d : Official.MemberDecl) (t : Official.AuxType) :
    Prop :=
  t.name = d.name ∧ Official.instPiParams d.type c.ps = .ok t.type ∧
    ∃ raws, d.ctors.mapM (fun x => Official.instPiParams x c.ps) = .ok raws ∧ CtorsOk c mem G p A raws t.ctors

/-- An auxiliary type in the elimination's state, for its map entry
`(J Ds, a)`: a whole-block copy of the stored inductive `I`'s block. -/
@[expose] def AuxTy (p : Prop) (A : List (Expr × Name)) (en : Expr × Name) (t : Official.AuxType) : Prop :=
  t.name = en.2 ∧ ∃ I J us ds, en.1 = Expr.mkAppN (.const J us) ds ∧ KeyPre c mem G I ds ∧
    J ∈ Official.blockOf c I ∧
    (∀ J' ∈ Official.blockOf c I, ∃ a', (Expr.mkAppN (.const J' us) ds, a') ∈ A) ∧
    ∃ raws, Official.CopyOk c us ds J ⟨t.name, t.type, raws⟩ ∧ CtorsOk c mem G p A raws t.ctors

/-- **The elimination's invariant** at queue position `q`: the types are
the members followed by the auxiliary entries, in order; the auxiliary
names are `auxName 1, 2, …`; every type below `q` is replaced against the
current map, the others are raw. -/
structure EInv (decl : List Official.MemberDecl) (q : Nat) (s : Official.ElimSt) : Prop where
  size : s.types.size = decl.length + s.aux.length
  next : s.next = s.aux.length + 1
  names : ∀ j (h : j < s.aux.length), s.aux[j].2 = c.auxName (j + 1)
  mems : ∀ i (h : i < decl.length), ∃ t, s.types.toList[i]? = some t ∧
    MemTy c mem G (i < q) s.aux decl[i] t
  auxs : ∀ j (h : j < s.aux.length), ∃ t, s.types.toList[decl.length + j]? = some t ∧
    AuxTy c mem G (decl.length + j < q) s.aux s.aux[j] t

variable {c mem G}

theorem CtorsOk.mono {p : Prop} {A B : List (Expr × Name)} {raws cs : List Expr} (hAB : Compat A B)
    (h : CtorsOk c mem G p A raws cs) : CtorsOk c mem G p B raws cs := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun hp => ?_, h3⟩
  obtain ⟨hs, hcs⟩ := h2 hp
  refine ⟨fun u hu => (sigmaAll_compat hAB u (hs u hu)).1, ?_⟩
  rw [hcs]
  exact List.map_congr_left fun u hu => (sigmaAll_compat hAB u (hs u hu)).2.symm

theorem AuxTy.mono {p : Prop} {A B : List (Expr × Name)} {en : Expr × Name} {t : Official.AuxType}
    (hAB : A <+: B) (h : AuxTy c mem G p A en t) : AuxTy c mem G p B en t := by
  obtain ⟨hn, I, J, us, ds, hk, hpre, hJ, hblk, raws, hcp, hco⟩ := h
  obtain ⟨X, rfl⟩ := hAB
  refine ⟨hn, I, J, us, ds, hk, hpre, hJ, fun J' hJ' => ?_, raws, hcp, hco.mono (Compat.append _ _)⟩
  obtain ⟨a', ha'⟩ := hblk J' hJ'
  exact ⟨a', List.mem_append_left _ ha'⟩

theorem MemTy.mono {p : Prop} {A B : List (Expr × Name)} {d : Official.MemberDecl} {t : Official.AuxType}
    (hAB : Compat A B) (h : MemTy c mem G p A d t) : MemTy c mem G p B d t := by
  obtain ⟨hn, hty, raws, hr, hco⟩ := h
  exact ⟨hn, hty, raws, hr, hco.mono hAB⟩

variable (c mem G) in
/-- What the elimination's invariant is preserved under: the auxiliary
names are fresh (`G`, off the members), the declaration's and the
containers' constructor types and the parameters mention none of them. -/
structure EHyp (decl : List Official.MemberDecl) : Prop where
  auxG : ∀ k, G (c.auxName k) = true
  memG : ∀ n, mem.contains n = true → G n = false
  declNames : decl.map (·.name) = mem
  ps : ∀ p ∈ c.ps, NoAux G p
  declAux : ∀ d ∈ decl, ∀ x ∈ d.ctors, NoAux G x
  ctorAux : ∀ J x, x ∈ c.ctorsOf J → NoAux G x.1.type

variable {decl : List Official.MemberDecl} {q : Nat}

theorem getElem_of_getElem?_some {α : Type} {l : List α} {i : Nat} {t : α} (h : l[i]? = some t)
    {hi : i < l.length} : l[i] = t := by
  rw [List.getElem?_eq_getElem hi] at h; exact Option.some.inj h

/-- The state's type names: the members', then the auxiliary names. -/
theorem EInv.names_eq {s : Official.ElimSt} (hH : EHyp c mem G decl) (hI : EInv c mem G decl q s) :
    s.names = mem ++ s.aux.map (·.2) := by
  have hlen : s.names.length = (mem ++ s.aux.map (·.2)).length := by
    simp only [Official.ElimSt.names, List.length_map, Array.length_toList, List.length_append,
      hI.size, ← hH.declNames]
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  simp only [Official.ElimSt.names, List.getElem_map]
  rcases Nat.lt_or_ge i decl.length with hi | hi
  · obtain ⟨t, ht, hn, -⟩ := hI.mems i hi
    have hi' : i < mem.length := by rw [← hH.declNames]; simpa using hi
    rw [List.getElem_append_left hi', getElem_of_getElem?_some ht, hn]
    simp [← hH.declNames]
  · have hj : i - decl.length < s.aux.length := by
      simp only [List.length_append, List.length_map, ← hH.declNames] at h2; omega
    obtain ⟨t, ht, hn, -⟩ := hI.auxs (i - decl.length) hj
    have hi' : ¬ i < mem.length := by rw [← hH.declNames]; simpa using hi
    rw [List.getElem_append_right (by simpa [← hH.declNames] using hi)]
    rw [show decl.length + (i - decl.length) = i by omega] at ht
    rw [getElem_of_getElem?_some ht, hn]
    simp [← hH.declNames]

theorem EInv.names_congr {s : Official.ElimSt} (hH : EHyp c mem G decl) (hI : EInv c mem G decl q s) :
    ∀ n, G n = false → mem.contains n = s.names.contains n := by
  intro n hn
  rw [hI.names_eq hH, List.contains_append]
  suffices (s.aux.map (·.2)).contains n = false by rw [this, Bool.or_false]
  rw [Bool.eq_false_iff]
  intro hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  rw [hI.names j hj, hH.auxG] at hn
  exact Bool.noConfusion hn

theorem Compat.of_prefix {A B : List (Expr × Name)} (h : A <+: B) : Compat A B := by
  obtain ⟨X, rfl⟩ := h; exact Compat.append _ _

theorem getElem?_prefix {α : Type} {l L : List α} (h : l <+: L) {i : Nat} (hi : i < l.length) :
    L[i]? = l[i]? := by
  obtain ⟨X, rfl⟩ := h
  exact List.getElem?_append_left hi

/-- **The invariant under a whole-block copy** (`copyBlock` of the head's
recorded block, at a key official has just met). -/
theorem EInv.copyBlock {s s' : Official.ElimSt} (hH : EHyp c mem G decl) (hI : EInv c mem G decl q s)
    (hq : q ≤ s.types.size) {I : Name} {us : List Level} {ds : List Expr}
    (hpre : KeyPre c mem G I ds)
    (hcb : (Official.copyBlock c us ds (Official.blockOf c I)).run s = .ok ((), s')) :
    EInv c mem G decl q s' ∧ s.aux <+: s'.aux ∧ s.types.toList <+: s'.types.toList := by
  obtain ⟨hn, ha, ts, hts, htl, hj⟩ := Official.copyBlock_spec _ _ _ hcb
  generalize hJs : Official.blockOf c I = Js at hn ha hj htl
  have hpA : s.aux <+: s'.aux := ⟨_, ha.symm⟩
  have hpT : s.types.toList <+: s'.types.toList := ⟨_, hts.symm⟩
  have hsz : s.types.toList.length = decl.length + s.aux.length := by simpa using hI.size
  have hAl : s'.aux.length = s.aux.length + Js.length := by rw [ha]; simp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hpA, hpT⟩
  · rw [← Array.length_toList, hts, List.length_append, hsz, htl, hAl]; omega
  · rw [hn, hI.next, hAl]; omega
  · intro j hjl
    rcases Nat.lt_or_ge j s.aux.length with hlt | hge
    · have := hI.names j hlt
      rw [← this]
      congr 1
      simp only [ha]
      rw [List.getElem_append_left hlt]
    · simp only [ha]
      rw [List.getElem_append_right hge]
      simp only [List.getElem_mapIdx]
      congr 1
      rw [hI.next]; omega
  · intro i hi
    obtain ⟨t, ht, hm⟩ := hI.mems i hi
    exact ⟨t, by rw [getElem?_prefix hpT (by omega)]; exact ht, hm.mono (Compat.of_prefix hpA)⟩
  · intro j hjl
    rcases Nat.lt_or_ge j s.aux.length with hlt | hge
    · obtain ⟨t, ht, hm⟩ := hI.auxs j hlt
      refine ⟨t, by rw [getElem?_prefix hpT (by omega)]; exact ht, ?_⟩
      have he : s'.aux[j] = s.aux[j] := by simp only [ha]; rw [List.getElem_append_left hlt]
      rw [he]
      exact AuxTy.mono hpA hm
    · have hk : j - s.aux.length < Js.length := by omega
      obtain ⟨t, ht, htn, hcp⟩ := hj _ hk
      refine ⟨t, ?_, ?_⟩
      · rw [hts, List.getElem?_append_right (by omega)]
        rw [show decl.length + j - s.types.toList.length = j - s.aux.length by omega]
        exact ht
      have he : s'.aux[j] = (Expr.mkAppN (.const Js[j - s.aux.length] us) ds,
          c.auxName (s.next + (j - s.aux.length))) := by
        simp only [ha]; rw [List.getElem_append_right hge]; simp
      rw [he]
      obtain ⟨cv, caps, hf, hty, hcs⟩ := hcp
      refine ⟨htn, I, Js[j - s.aux.length], us, ds, rfl, hpre, by rw [hJs]; exact List.getElem_mem hk, ?_, t.ctors,
        ⟨cv, caps, hf, hty, hcs⟩, ?_, fun h => absurd h (by have := hI.size; omega), fun _ => rfl⟩
      · intro J' hJ'
        rw [hJs] at hJ'
        obtain ⟨k, hkl, rfl⟩ := List.getElem_of_mem hJ'
        refine ⟨c.auxName (s.next + k), ?_⟩
        rw [ha]
        refine List.mem_append_right _ ?_
        rw [List.mem_iff_getElem]
        exact ⟨k, by simpa using hkl, by simp⟩
      · intro u hu
        obtain ⟨x, hx, hxu⟩ := Official.mapM_except_mem' hcs u hu
        exact noAux_instPisWith ds _ u (fun y hy => (hpre.2.2.1 y hy).2)
          (noAux_instantiateLevelParams G _ (hH.ctorAux _ x hx)) (Official.instPiParams_ok.mp hxu)

/-- **`replaceIfNested` keeps the invariant**, and its answer is official's
test over the MEMBERS (the term free of auxiliary names): no nested
occurrence, or one whose key the grown map names. -/
theorem EInv.replaceIfNested {s s' : Official.ElimSt} {e : Expr} {r : Option Expr}
    (hH : EHyp c mem G decl) (hI : EInv c mem G decl q s) (hq : q ≤ s.types.size) (he : NoAux G e)
    (h : (Official.replaceIfNested c e).run s = .ok (r, s')) :
    EInv c mem G decl q s' ∧ s.aux <+: s'.aux ∧ s.types.toList <+: s'.types.toList ∧
      (r = none → Official.isNestedApp c mem e = .ok none) ∧
      ∀ x, r = some x → ∃ I us np args a,
        Official.isNestedApp c mem e = .ok (some (I, us, np, args)) ∧
        s'.aux.lookup (Official.keyOf I us np args) = some a ∧
        x = Expr.mkAppN (Expr.mkAppN (.const a c.lvls) c.ps) (args.drop np) := by
  have hcg : Official.isNestedApp c s.names e = Official.isNestedApp c mem e :=
    (isNestedApp_congr (fun n hn => (hI.names_congr hH n hn).symm) he)
  rcases Official.replaceIfNested_spec h with ⟨rfl, hN, rfl⟩ | ⟨I, us, np, args, a, rfl, hN, hl, hs⟩
  · exact ⟨hI, List.prefix_refl _, List.prefix_refl _, fun _ => hcg ▸ hN, fun x hx => nomatch hx⟩
  · rw [hcg] at hN
    have hfin : ∀ x, some (Expr.mkAppN (Expr.mkAppN (.const a c.lvls) c.ps) (args.drop np)) = some x →
        ∃ I us np args a, Official.isNestedApp c mem e = .ok (some (I, us, np, args)) ∧
        s'.aux.lookup (Official.keyOf I us np args) = some a ∧
        x = Expr.mkAppN (Expr.mkAppN (.const a c.lvls) c.ps) (args.drop np) :=
      fun x hx => ⟨I, us, np, args, a, hN, hl, (Option.some.inj hx).symm⟩
    rcases hs with rfl | hcb
    · exact ⟨hI, List.prefix_refl _, List.prefix_refl _, (fun h => nomatch h), hfin⟩
    · obtain ⟨hfn, hargs, hquot, cv, caps, hf, hnp, hle, hocc, hbv⟩ := Official.isNestedApp_some hN
      have hna : ∀ x ∈ args.take np, NoAux G x := fun x hx =>
        noAux_getAppArgs e he x (hargs ▸ List.mem_of_mem_take hx)
      have hpre : KeyPre c mem G I (args.take np) :=
        ⟨⟨cv, caps, hf, by simp [List.length_take]; omega⟩, hquot, fun x hx => ⟨hbv x hx, hna x hx⟩, hocc⟩
      obtain ⟨hI', hpA, hpT⟩ := hI.copyBlock hH hq hpre hcb
      exact ⟨hI', hpA, hpT, (fun h => nomatch h), hfin⟩

theorem stateT_bind_ok {σ ε α β : Type} {x : StateT σ (Except ε) α} {f : α → StateT σ (Except ε) β}
    {s s' : σ} {r : β} (h : (x >>= f).run s = .ok (r, s')) :
    ∃ a s1, x.run s = .ok (a, s1) ∧ (f a).run s1 = .ok (r, s') := by
  simp only [StateT.run_bind] at h
  rcases hx : x.run s with e | ⟨a, s1⟩
  · simp [hx, bind, Except.bind] at h
  · simp only [hx, bind, Except.bind] at h
    exact ⟨a, s1, rfl, h⟩

theorem stateT_pure_ok {σ ε α : Type} {a r : α} {s s' : σ}
    (h : (pure a : StateT σ (Except ε) α).run s = .ok (r, s')) : r = a ∧ s' = s := by
  have : (pure a : StateT σ (Except ε) α).run s = .ok (a, s) := rfl
  rw [this] at h
  cases h; exact ⟨rfl, rfl⟩

theorem size_le_of_prefix {s s' : Official.ElimSt} (h : s.types.toList <+: s'.types.toList) :
    s.types.size ≤ s'.types.size := by
  simpa using h.length_le

/-- The facts one `replaceAll` step yields. -/
@[expose] def RAOk (decl : List Official.MemberDecl) (q : Nat) (s s' : Official.ElimSt) (e r : Expr) :
    Prop :=
  EInv c mem G decl q s' ∧ s.aux <+: s'.aux ∧ s.types.toList <+: s'.types.toList ∧
    SigOk c mem s'.aux e ∧ sigmaAll c mem s'.aux e = r

/-- Two `replaceAll` steps in a row: the first's facts carried past the
second's growth. -/
theorem raOk_two {s s1 s2 : Official.ElimSt} {x y rx ry : Expr}
    (h1 : RAOk (c := c) (mem := mem) (G := G) decl q s s1 x rx)
    (h2 : RAOk (c := c) (mem := mem) (G := G) decl q s1 s2 y ry) :
    EInv c mem G decl q s2 ∧ s.aux <+: s2.aux ∧ s.types.toList <+: s2.types.toList ∧
      SigOk c mem s2.aux x ∧ sigmaAll c mem s2.aux x = rx ∧ SigOk c mem s2.aux y ∧
      sigmaAll c mem s2.aux y = ry := by
  obtain ⟨-, hA1, hT1, hs1, he1⟩ := h1
  obtain ⟨hI2, hA2, hT2, hs2, he2⟩ := h2
  obtain ⟨hs1', he1'⟩ := sigmaAll_compat (Compat.of_prefix hA2) x hs1
  exact ⟨hI2, hA1.trans hA2, hT1.trans hT2, hs1', he1'.trans he1, hs2, he2⟩

/-- **`replaceAll` computes `sigmaAll` against the map it ends with**, and
keeps the invariant. -/
theorem EInv.replaceAll (hH : EHyp c mem G decl) : ∀ (e : Expr) {s s' : Official.ElimSt} {r : Expr},
    EInv c mem G decl q s → q ≤ s.types.size → NoAux G e →
    (Official.replaceAll c e).run s = .ok (r, s') → RAOk (c := c) (mem := mem) (G := G) decl q s s' e r := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨o, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨hI1, hA1, hT1, hnone, hsome⟩ := hI.replaceIfNested hH hq he h1
    rcases o with _ | x
    · have hN := hnone rfl
      simp only at h2
      obtain ⟨rf, s2, h3, h4⟩ := stateT_bind_ok h2
      obtain ⟨ra, s3, h5, h6⟩ := stateT_bind_ok h4
      obtain ⟨rfl, rfl⟩ := stateT_pure_ok h6
      have hq1 := Nat.le_trans hq (size_le_of_prefix hT1)
      have hf := ihf hI1 hq1 he.1 h3
      have hq2 := Nat.le_trans hq1 (size_le_of_prefix hf.2.2.1)
      have ha := iha hf.1 hq2 he.2 h5
      obtain ⟨hI3, hA, hT, hsf, hef, hsa, hea⟩ := raOk_two hf ha
      refine ⟨hI3, hA1.trans hA, hT1.trans hT, ?_, ?_⟩
      · simp only [SigOk, hN]; exact ⟨hsf, hsa⟩
      · simp only [sigmaAll, hN, hef, hea]
    · obtain ⟨I, us, np, args, a', hN, hl, rfl⟩ := hsome x rfl
      simp only at h2
      obtain ⟨rfl, rfl⟩ := stateT_pure_ok h2
      refine ⟨hI1, hA1, hT1, ?_, ?_⟩
      · simp only [SigOk, hN]; simp only [Official.keyOf] at hl; simp [hl]
      · simp only [sigmaAll, hN]; simp only [Official.keyOf] at hl; simp [hl]
  | lam t b m iht ihb =>
    intro s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨r1, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨r2, s2, h3, h4⟩ := stateT_bind_ok h2
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h4
    have ht := iht hI hq he.1 h1
    have hb := ihb ht.1 (Nat.le_trans hq (size_le_of_prefix ht.2.2.1)) he.2 h3
    obtain ⟨hI3, hA, hT, hs1, he1, hs2, he2⟩ := raOk_two ht hb
    exact ⟨hI3, hA, hT, ⟨hs1, hs2⟩, by simp only [sigmaAll, he1, he2]⟩
  | forallE t b m iht ihb =>
    intro s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨r1, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨r2, s2, h3, h4⟩ := stateT_bind_ok h2
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h4
    have ht := iht hI hq he.1 h1
    have hb := ihb ht.1 (Nat.le_trans hq (size_le_of_prefix ht.2.2.1)) he.2 h3
    obtain ⟨hI3, hA, hT, hs1, he1, hs2, he2⟩ := raOk_two ht hb
    exact ⟨hI3, hA, hT, ⟨hs1, hs2⟩, by simp only [sigmaAll, he1, he2]⟩
  | letE t v b iht ihv ihb =>
    intro s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨r1, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨r2, s2, h3, h4⟩ := stateT_bind_ok h2
    obtain ⟨r3, s3, h5, h6⟩ := stateT_bind_ok h4
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h6
    have ht := iht hI hq he.1 h1
    have hv := ihv ht.1 (Nat.le_trans hq (size_le_of_prefix ht.2.2.1)) he.2.1 h3
    have hq2 := Nat.le_trans (Nat.le_trans hq (size_le_of_prefix ht.2.2.1)) (size_le_of_prefix hv.2.2.1)
    have hb := ihb hv.1 hq2 he.2.2 h5
    obtain ⟨-, hA, hT, hs1, he1, hs2, he2⟩ := raOk_two ht hv
    have htv : RAOk (c := c) (mem := mem) (G := G) decl q s s2 t r1 :=
      ⟨hv.1, hA, hT, hs1, he1⟩
    obtain ⟨hI3, hA', hT', hs1', he1', hs3, he3⟩ := raOk_two htv hb
    obtain ⟨hs2', he2'⟩ := sigmaAll_compat (Compat.of_prefix hb.2.1) v hs2
    exact ⟨hI3, hA', hT', ⟨hs1', hs2', hs3⟩, by simp only [sigmaAll, he1', he2'.trans he2, he3]⟩
  | proj sn i x ih =>
    intro s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨r1, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h2
    obtain ⟨hI1, hA, hT, hs, he1⟩ := ih hI hq he h1
    exact ⟨hI1, hA, hT, hs, by simp only [sigmaAll, he1]⟩
  | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ =>
    intro s s' r hI hq he h
    simp only [Official.replaceAll] at h
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h
    exact ⟨hI, List.prefix_refl _, List.prefix_refl _, trivial, rfl⟩

/-- **`replaceAll` over a constructor list.** -/
theorem EInv.mapM_replaceAll (hH : EHyp c mem G decl) : ∀ (l : List Expr) {s s' : Official.ElimSt}
    {cs : List Expr}, EInv c mem G decl q s → q ≤ s.types.size → (∀ u ∈ l, NoAux G u) →
    (l.mapM (Official.replaceAll c)).run s = .ok (cs, s') →
    EInv c mem G decl q s' ∧ s.aux <+: s'.aux ∧ s.types.toList <+: s'.types.toList ∧
      (∀ u ∈ l, SigOk c mem s'.aux u) ∧ cs = l.map (sigmaAll c mem s'.aux)
  | [], s, s', cs, hI, _, _, h => by
    rw [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h
    exact ⟨hI, List.prefix_refl _, List.prefix_refl _, by simp, rfl⟩
  | u :: l, s, s', cs, hI, hq, hl, h => by
    rw [List.mapM_cons] at h
    obtain ⟨r1, s1, h1, h2⟩ := stateT_bind_ok h
    obtain ⟨r2, s2, h3, h4⟩ := stateT_bind_ok h2
    obtain ⟨rfl, rfl⟩ := stateT_pure_ok h4
    obtain ⟨hI1, hA1, hT1, hs1, he1⟩ := hI.replaceAll hH u hq (hl u List.mem_cons_self) h1
    obtain ⟨hI2, hA2, hT2, hs2, he2⟩ := EInv.mapM_replaceAll hH l hI1
      (Nat.le_trans hq (size_le_of_prefix hT1)) (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h3
    obtain ⟨hs1', he1'⟩ := sigmaAll_compat (Compat.of_prefix hA2) u hs1
    refine ⟨hI2, hA1.trans hA2, hT1.trans hT2, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hs1'
      · exact hs2 x hx
    · rw [he2, List.map_cons, he1', he1]

theorem CtorsOk.skip {i q : Nat} {A : List (Expr × Name)} {raws cs : List Expr} (hi : i ≠ q)
    (h : CtorsOk c mem G (i < q) A raws cs) : CtorsOk c mem G (i < q + 1) A raws cs := by
  have : (i < q + 1) = (i < q) := propext (by omega)
  rw [this]; exact h

theorem CtorsOk.done {q : Nat} {A : List (Expr × Name)} {raws cs cs' : List Expr}
    (h : CtorsOk c mem G (q < q) A raws cs) (hs : ∀ u ∈ cs, SigOk c mem A u)
    (he : cs' = cs.map (sigmaAll c mem A)) : CtorsOk c mem G (q < q + 1) A raws cs' := by
  obtain ⟨h1, -, h3⟩ := h
  have hr := h3 (Nat.lt_irrefl q)
  subst hr
  exact ⟨h1, fun _ => ⟨hs, he⟩, fun h => absurd (Nat.lt_succ_self q) h⟩

/-- **One type processed**: the invariant moves past `q`. -/
theorem EInv.setDone {s : Official.ElimSt} {t : Official.AuxType} {cs : List Expr}
    (hI : EInv c mem G decl q s) (ht : s.types.toList[q]? = some t)
    (hs : ∀ u ∈ t.ctors, SigOk c mem s.aux u) (he : cs = t.ctors.map (sigmaAll c mem s.aux)) :
    EInv c mem G decl (q + 1) { s with types := s.types.set! q { t with ctors := cs } } := by
  have hget : ∀ i, ({ s with types := s.types.set! q { t with ctors := cs } } : Official.ElimSt).types.toList[i]?
      = if q = i then some { t with ctors := cs } else s.types.toList[i]? := by
    intro i
    simp only [Array.toList_set!, List.getElem?_set]
    by_cases hqi : q = i
    · subst hqi
      have : q < s.types.toList.length := by
        rcases Nat.lt_or_ge q s.types.toList.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at ht; cases ht
      simpa using this
    · simp [hqi]
  refine ⟨by simpa using hI.size, hI.next, hI.names, ?_, ?_⟩
  · intro i hi
    obtain ⟨ti, hti, hn, hty, raws, hr, hco⟩ := hI.mems i hi
    rw [hget i]
    by_cases hqi : q = i
    · subst hqi
      rw [ht] at hti; cases hti
      exact ⟨{ t with ctors := cs }, by simp, hn, hty, raws, hr, hco.done hs he⟩
    · rw [if_neg hqi]
      exact ⟨ti, hti, hn, hty, raws, hr, hco.skip (Ne.symm hqi)⟩
  · intro j hj
    obtain ⟨ti, hti, hn, I, J, us, ds, hk, hpre, hJ, hblk, raws, hcp, hco⟩ := hI.auxs j hj
    rw [hget]
    by_cases hqi : q = decl.length + j
    · rw [if_pos hqi]
      rw [← hqi] at hti hco ⊢
      rw [ht] at hti; cases hti
      exact ⟨{ t with ctors := cs }, rfl, hn, I, J, us, ds, hk, hpre, hJ, hblk, raws, hcp, hco.done hs he⟩
    · rw [if_neg hqi]
      exact ⟨ti, hti, hn, I, J, us, ds, hk, hpre, hJ, hblk, raws, hcp, hco.skip (Ne.symm hqi)⟩

/-- A type at the queue position is raw: its constructors are free of
auxiliary names. -/
theorem EInv.raw {s : Official.ElimSt} {t : Official.AuxType} (hI : EInv c mem G decl q s)
    (ht : s.types.toList[q]? = some t) : ∀ u ∈ t.ctors, NoAux G u := by
  have hlt : q < s.types.toList.length := by
    rcases Nat.lt_or_ge q s.types.toList.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at ht; cases ht
  rcases Nat.lt_or_ge q decl.length with hi | hi
  · obtain ⟨ti, hti, -, -, raws, -, h1, -, h3⟩ := hI.mems q hi
    rw [ht] at hti; cases hti
    rw [h3 (Nat.lt_irrefl q)]; exact h1
  · have hj : q - decl.length < s.aux.length := by
      have := hI.size; simp at hlt; omega
    obtain ⟨ti, hti, -, -, -, -, -, -, -, -, -, raws, -, h1, -, h3⟩ := hI.auxs _ hj
    rw [show decl.length + (q - decl.length) = q by omega, ht] at hti
    cases hti
    rw [h3 (by omega)]; exact h1

/-- **The elimination loop ends with every type replaced** against the
final map. -/
theorem EInv.elimLoop (hH : EHyp c mem G decl) : ∀ (fuel q : Nat) {s st : Official.ElimSt},
    EInv c mem G decl q s → q ≤ s.types.size → (Official.elimLoop c fuel q).run s = .ok ((), st) →
    ∃ q', st.types.size ≤ q' ∧ EInv c mem G decl q' st
  | 0, q, s, st, _, _, h => by
    simp only [Official.elimLoop] at h
    cases h
  | fuel + 1, q, s, st, hI, hq, h => by
    simp only [Official.elimLoop] at h
    obtain ⟨s0, s0', h0, h1⟩ := stateT_bind_ok h
    have e1 : s0 = s := by cases h0; rfl
    have e2 : s0' = s := by cases h0; rfl
    rw [e1, e2] at h1
    rcases ht : s.types[q]? with _ | t
    · simp only [ht] at h1
      obtain ⟨-, rfl⟩ := stateT_pure_ok h1
      exact ⟨q, by simpa using ht, hI⟩
    simp only [ht] at h1
    obtain ⟨cs, s2, h2, h3⟩ := stateT_bind_ok h1
    obtain ⟨u, s3, h4, h5⟩ := stateT_bind_ok h3
    have hs3 : s3 = { s2 with types := s2.types.set! q { t with ctors := cs } } := by
      cases h4; rfl
    subst hs3
    have hqlt : q < s.types.size := by
      rcases Nat.lt_or_ge q s.types.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at ht; cases ht
    have htl : s.types.toList[q]? = some t := by simpa using ht
    have hna := hI.raw htl
    obtain ⟨hI2, -, hT2, hs2, he2⟩ := hI.mapM_replaceAll hH t.ctors hq hna h2
    have ht2 : s2.types.toList[q]? = some t := by rw [getElem?_prefix hT2 (by simpa using hqlt)]; exact htl
    have hI3 := hI2.setDone ht2 hs2 he2
    exact EInv.elimLoop hH fuel (q + 1) hI3 (by simp only [Array.size_set!]; exact Nat.lt_of_lt_of_le hqlt (size_le_of_prefix hT2)) h5

theorem mapM_except_getElem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {rs : List β}, l.mapM f = .ok rs →
      rs.length = l.length ∧ ∀ i (h : i < l.length), ∃ r, rs[i]? = some r ∧ f l[i] = .ok r
  | [], rs, h => by
    simp [List.mapM_nil, pure, Except.pure] at h; subst h; exact ⟨rfl, fun i h => by simp at h⟩
  | a :: l, rs, h => by
    rw [List.mapM_cons] at h
    rcases ha : f a with e | r
    · simp [ha, bind, Except.bind] at h
    · rcases hl : l.mapM f with e | rs'
      · simp [ha, hl, bind, Except.bind] at h
      · simp [ha, hl, bind, Except.bind, pure, Except.pure] at h
        subst h
        obtain ⟨hlen, hi⟩ := mapM_except_getElem hl
        refine ⟨by simp [hlen], fun i hil => ?_⟩
        cases i with
        | zero => exact ⟨r, rfl, ha⟩
        | succ i =>
          obtain ⟨r', h1, h2⟩ := hi i (by simpa using hil)
          exact ⟨r', by simpa using h1, by simpa using h2⟩

/-- **THE ELIMINATION'S RESULT**: official's `elimNested` ends with every
type — the members, then one per auxiliary entry, in order — replaced
against the FINAL map (`sigmaAll`), with the invariant's bookkeeping. -/
theorem EInv.elimNested (hH : EHyp c mem G decl) {fuel : Nat} {st : Official.ElimSt}
    (h : Official.elimNested c decl fuel = .ok st) :
    ∃ q', st.types.size ≤ q' ∧ EInv c mem G decl q' st := by
  simp only [Official.elimNested, bind, Except.bind] at h
  split at h
  · cases h
  rename_i tys htys
  rcases hl : (Official.elimLoop c fuel 0).run { types := tys.toArray } with e | ⟨⟨⟩, st'⟩
  · simp [hl] at h
  simp only [hl, pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hlen, hi⟩ := mapM_except_getElem htys
  refine EInv.elimLoop hH fuel 0 ⟨by simpa using hlen, rfl, fun j hj => by simp at hj, ?_,
    fun j hj => by simp at hj⟩ (Nat.zero_le _) hl
  intro i hil
  obtain ⟨r, hr, hf⟩ := hi i hil
  refine ⟨r, by simpa using hr, ?_⟩
  rcases hty : Official.instPiParams decl[i].type c.ps with e | ty
  · simp [hty] at hf
  rcases hcs : decl[i].ctors.mapM (fun t => Official.instPiParams t c.ps) with e | cs
  · simp [hty, hcs] at hf
  simp only [hty, hcs, pure, Except.pure, Except.ok.injEq] at hf
  subst hf
  refine ⟨rfl, hty, cs, hcs, fun u hu => ?_, fun h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩
  obtain ⟨x, hx, hxu⟩ := Official.mapM_except_mem' hcs u hu
  exact noAux_instPisWith c.ps _ u hH.ps (hH.declAux _ (List.getElem_mem hil) x hx)
    (Official.instPiParams_ok.mp hxu)

end Inv

end ConLeche
