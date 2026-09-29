module

public import ConLeche.Kernel.Inductives.Positivity

public section

/-!
# The in-progress test reads only `active`

`nestContKey` rejects an instantiation met as a CONSTANT while it is in
progress: in the run's `active` list (every frame being walked, the
frames walked at the empty stack included).  Until lane RPCLEAN it also
tested the frame stack `prog` (`prog.any (·.key == key)`).  Every frame
stack entry is a key of an enclosing `nestContNew`'s group, which that
`nestContNew` pushed to `active` for the duration of its frame
(`ProgActive`), so the second test was implied.

This file keeps that older walk as a SPECIFICATION — `nestContKeyP`
(the frame-stack test, then `nestContKey`), and `nestContP`/`nestPosP`,
`nestCont`/`nestPos` verbatim with the older key step — and proves it
EQUAL to the walk at every state satisfying `ProgActive`
(`nestPosP_eq`), in particular at the walk's entries (the empty stack,
`nestPosP_eq_nil`): deleting the test moved no verdict.  At the pure
monad; the executed run is the same function at the index-threaded
operations.  A result, not a lemma: nothing consumes it.
-/

namespace ConLeche

/-- **The frame stack is in progress**: every entry's key is in `active`. -/
@[expose] def ProgActive (prog : List NestHole) (st : NestState) : Prop :=
  ∀ h ∈ prog, h.key ∈ st.active

/-- The older key step: the frame-stack test, then the walk's own. -/
@[expose] def nestContKeyP (ctx : NestCtx) (ops : CheckerOps CheckM) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) : CheckM (NestFieldKind × NestState) :=
  if prog.any (·.key == ⟨n, us, ds⟩) || st.active.contains ⟨n, us, ds⟩ then
    throw (.invalid "nested positivity: non valid occurrence of the datatypes being \
      declared (an instantiation in progress, reached through reduction)")
  else nestContKey ctx ops env rec prog kb n us ds nPc cty st

/-- `nestCont` with the older key step. -/
@[expose] def nestContP (ctx : NestCtx) (ops : CheckerOps CheckM) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (args : List Expr)
    (st : NestState) : CheckM (NestFieldKind × NestState) := do
  let q ← unwrapOr (nestContainer ctx n) nestNonValid
  if args.length < q.1 ||
      !(args.drop q.1).all (fun x => !x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length)) then
    throw nestNonValid
  -- `Quot` is stored as an `.indInfo` but is no inductive for
  -- official (`is_nested_inductive_app` asks `is_inductive()`):
  -- the one name read here.  Every other basis type (`Eq`, `Nat`,
  -- `PUnit`, `Empty`, `False`, and `And`) is a container like any
  -- stored inductive.
  if n == quotName then throw nestNonValid
  unless (args.take q.1).all (fun x => x.bvarB == 0 && x.fvarB ≤ ctx.hiAt prog.length) do
    throw (.invalid "nested positivity: nested inductive datatypes parameters \
      cannot contain local variables")
  -- the instance is FULLY applied: the container case
  -- compares the container's family at the index tuple, and a partial
  -- application is a function, whose graph does not grow with its values.
  -- A field's domain is a type, so a checked constructor never has one.
  let ni ← nestInstType ctx (ctx.hiAt prog.length) ⟨n, us, args.take q.1⟩
  unless args.length == q.1 + ni.1 do
    throw (.invalid "nested positivity: type expected (a container instance that is not \
      fully applied)")
  nestContKeyP ctx ops env rec prog kb n us (args.take q.1) q.1 ni.2 st

/-- `nestPos` with the older key step. -/
@[expose] def nestPosP (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) :
    Nat → List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)
  | 0, _, _, _, _, _ => throw (.notImplemented "nested positivity: fuel")
  | fuel + 1, prog, dep, kb, e, st => do
    let hi := ctx.hiAt prog.length
    let w ← ops.whnf env dep e
    -- `const`: the reduct mentions no member and no hole; the normal
    -- form is the input when it mentions none either, else the reduct
    if !w.nestOcc ctx.names ctx.nP hi then
      return (.ordinary, (if e.nestOcc ctx.names ctx.nP hi then w else e), st)
    match w with
    | .forallE a b bm =>
      -- `pi`: the domain hole-free, the codomain positive
      if a.nestOcc ctx.names ctx.nP hi then
        throw (.invalid "nested positivity: non positive occurrence of the datatypes \
          being declared")
      let (k, nb, st) ←
        nestPosP ops env ctx fuel prog (dep + 1) (kb + 1) (b.instantiate1 (.fvar dep a)) st
      pure (k, .forallE a (nb.abstract1 dep) bm, st)
    | _ =>
      let args := w.getAppArgs
      match w.getAppFn with
      | .fvar i _ =>
        match nestHoleAt ctx prog i with
        | some h =>
          if h.key.ds.length ≤ args.length && args.take h.key.ds.length == h.key.ds &&
              (args.drop h.key.ds.length).all (fun x => !x.nestOcc ctx.names ctx.nP hi) &&
              args.length == nestArity ctx h.key.cname then
            return (if i < ctx.hiAt 0 then
                (if kb == 0 then .recursive (i - ctx.nP) else .reflexive (i - ctx.nP))
              else .inProgress, w, st)
          else throw nestNonValid
        | none => throw nestNonValid
      | .const n us =>
        -- a member constant left after the abstraction (other levels)
        if ctx.names.contains n then throw nestNonValid
        -- `contApp`: a stored inductive at a concrete instantiation
        let (k, st) ← nestContP ctx ops env (nestPosP ops env ctx fuel) prog kb n us args st
        pure (k, w, st)
      | _ => throw nestNonValid

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

/-- A walk that keeps `active`. -/
@[expose] def RecPres
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)) :
    Prop :=
  ∀ prog dep kb e st r, rec prog dep kb e st = .ok r → r.2.2.active = st.active

/-- Two walks that agree wherever the frame stack is in progress. -/
@[expose] def RecEq
    (rec₁ rec₂ : List NestHole → Nat → Nat → Expr → NestState →
      CheckM (NestFieldKind × Expr × NestState)) : Prop :=
  ∀ prog dep kb e st, ProgActive prog st → rec₁ prog dep kb e st = rec₂ prog dep kb e st

theorem ProgActive.of_active {prog : List NestHole} {st st' : NestState}
    (h : ProgActive prog st) (ha : st'.active = st.active) : ProgActive prog st' :=
  fun p hp => ha ▸ h p hp

variable {rec rec₁ rec₂ :
  List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}

/-! ## The walk keeps `active` -/

theorem nestFields_active (hrec : RecPres rec) (prog : List NestHole) (base : Nat)
    (err : CheckError) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) r,
      nestFields rec prog base err nF j cur st = .ok r → r.2.2.2.active = st.active
  | 0, _, _, st, r, h => by
    simp only [nestFields, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | nF + 1, j, cur, st, r, h => by
    unfold nestFields at h
    split at h
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      rename_i q hq
      split at h
      · simp at h
      rename_i q' hq'
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact (nestFields_active hrec prog base err nF _ _ _ _ hq').trans (hrec _ _ _ _ _ _ hq)
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem nestCtors_active (hrec : RecPres rec) (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (nPc : Nat) (sub : Name → List Level → Option Expr) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState) r,
      nestCtors ctx ops env (fun _ => rec) prog hi us ds nPc sub cs st = .ok r →
        r.2.active = st.active
  | [], st, st', h => by
    simp only [nestCtors, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | (cv, nF) :: cs, st, st', h => by
    simp only [nestCtors, bind, Except.bind] at h
    split at h
    · split at h
      · simp at h
      split at h
      · simp at h
      split at h
      · simp at h
      split at h
      · simp at h
      rename_i r hr
      obtain ⟨ks, nds, cur, st₁⟩ := r
      dsimp only at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      split at h
      · split at h
        · simp at h
        rename_i r' hr'
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact (nestCtors_active hrec prog hi us ds nPc sub cs _ _ hr').trans
          (nestFields_active hrec prog hi _ nF 0 _ st _ hr)
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem nestFrame_active (hrec : RecPres rec) {prog : List NestHole} {hi : Nat}
    {us : List Level} {ds : List Expr} {nPc : Nat} {grp : List (Name × Expr)}
    {st st' : NestState}
    (h : nestFrame ctx ops env rec prog hi us ds nPc grp st = .ok st') : st'.active = st.active := by
  simp only [nestFrame, bind, Except.bind] at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i q hq
  split at h
  · simp at h
  rename_i r hr
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact nestCtors_active hrec _ _ _ _ _ _ _ _ _ hr

/-- A new frame restores `active` itself, whatever its walk does. -/
theorem nestContNew_active {prog : List NestHole} {kb : Nat} {n : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat} {cty : Expr} {st : NestState} {r}
    (h : nestContNew ctx ops env rec prog kb n us ds nPc cty st = .ok r) :
    r.2.active = st.active := by
  simp only [nestContNew, bind, Except.bind] at h
  split at h
  · simp at h
  split at h
  · simp at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rfl

theorem nestContKey_active {prog : List NestHole} {kb : Nat} {n : Name} {us : List Level}
    {ds : List Expr} {nPc : Nat} {cty : Expr} {st : NestState} {r}
    (h : nestContKey ctx ops env rec prog kb n us ds nPc cty st = .ok r) :
    r.2.active = st.active := by
  unfold nestContKey at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  · exact nestContNew_active h

theorem nestCont_active {prog : List NestHole} {kb : Nat} {n : Name} {us : List Level}
    {args : List Expr} {st : NestState} {r}
    (h : nestCont ctx ops env rec prog kb n us args st = .ok r) : r.2.active = st.active := by
  simp only [nestCont, bind, Except.bind] at h
  split at h
  · simp at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · split at h
    · simp at h
    split at h
    · exact nestContKey_active h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The walk keeps `active`.** -/
theorem nestPos_active : ∀ fuel, RecPres (nestPos ops env ctx fuel)
  | 0, _, _, _, _, _, _, h => by simp [nestPos, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, prog, dep, kb, e, st, r, h => by
    simp only [nestPos, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i w hw
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
    split at h
    · split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      split at h
      · simp at h
      rename_i q hq
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact nestPos_active fuel _ _ _ _ _ q hq
    · split at h
      · repeat' (first
          | (simp [throw, throwThe, MonadExceptOf.throw] at h; done)
          | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
          | split at h)
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        split at h
        · simp at h
        rename_i q hq
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact nestCont_active hq
      · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The two walks agree where the frame stack is in progress -/

theorem bind_congr_ok {α β : Type} {x : CheckM α} {f g : α → CheckM β}
    (h : ∀ a, x = .ok a → f a = g a) : x >>= f = x >>= g := by
  cases x with
  | error e => rfl
  | ok a => exact h a rfl

theorem nestFields_eq (hrec : RecEq rec₁ rec₂) (hpres : RecPres rec₂) (prog : List NestHole)
    (base : Nat) (err : CheckError) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState), ProgActive prog st →
      nestFields rec₁ prog base err nF j cur st = nestFields rec₂ prog base err nF j cur st
  | 0, _, _, _, _ => rfl
  | nF + 1, j, cur, st, hpa => by
    simp only [nestFields]
    split
    · rw [hrec _ _ _ _ _ hpa]
      apply bind_congr_ok
      intro ⟨k, nd, st₁⟩ hq
      have hpa₁ := hpa.of_active (hpres _ _ _ _ _ _ hq)
      simp only [nestFields_eq hrec hpres prog base err nF (j + 1) _ st₁ hpa₁]
    · rfl

theorem nestCtors_eq (hrec : RecEq rec₁ rec₂) (hpres : RecPres rec₂) (prog : List NestHole)
    (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (sub : Name → List Level → Option Expr) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState), ProgActive prog st →
      nestCtors ctx ops env (fun _ => rec₁) prog hi us ds nPc sub cs st
        = nestCtors ctx ops env (fun _ => rec₂) prog hi us ds nPc sub cs st
  | [], _, _ => rfl
  | (cv, nF) :: cs, st, hpa => by
    simp only [nestCtors, nestFields_eq hrec hpres prog hi _ nF 0, hpa]
    split
    · refine bind_congr_ok fun _ _ => bind_congr_ok fun _ _ => bind_congr_ok fun _ _ =>
        bind_congr_ok fun q hq => ?_
      have hpa₁ := hpa.of_active (nestFields_active hpres _ _ _ _ _ _ _ _ hq)
      repeat' split
      all_goals first
        | rfl
        | rw [nestCtors_eq hrec hpres prog hi us ds nPc sub cs _ (hpa₁.of_active (by rfl))]
    · rfl

theorem nestFrame_eq (hrec : RecEq rec₁ rec₂) (hpres : RecPres rec₂) {prog : List NestHole}
    {hi : Nat} {us : List Level} {ds : List Expr} {nPc : Nat} {grp : List (Name × Expr)}
    {st : NestState} (hpa : ProgActive prog st)
    (hgrp : ∀ p ∈ grp, (⟨p.1, us, ds⟩ : NestKey) ∈ st.active) :
    nestFrame ctx ops env rec₁ prog hi us ds nPc grp st
      = nestFrame ctx ops env rec₂ prog hi us ds nPc grp st := by
  simp only [nestFrame]
  refine bind_congr_ok fun _ _ => bind_congr_ok fun q hq => ?_
  rw [nestCtors_eq hrec hpres _ _ _ _ _ _ _ _ fun h hh => ?_]
  rcases List.mem_append.mp hh with hh | hh
  · rw [List.mem_reverse, List.mem_mapIdx] at hh
    obtain ⟨i, hi, rfl⟩ := hh
    exact hgrp _ (List.getElem_mem hi)
  · exact hpa h hh

theorem nestContNew_eq (hrec : RecEq rec₁ rec₂) (hpres : RecPres rec₂) {prog : List NestHole}
    {kb : Nat} {n : Name} {us : List Level} {ds : List Expr} {nPc : Nat} {cty : Expr}
    {st : NestState} (hpa : ProgActive prog st) :
    nestContNew ctx ops env rec₁ prog kb n us ds nPc cty st
      = nestContNew ctx ops env rec₂ prog kb n us ds nPc cty st := by
  simp only [nestContNew]
  refine bind_congr_ok fun grp _ => ?_
  rw [nestFrame_eq hrec hpres (fun h hh => ?_) (fun p hp => ?_)]
  · unfold nestWalkStack at hh
    split at hh
    · exact nomatch hh
    · exact List.mem_append_right _ (hpa h hh)
  · exact List.mem_append_left _ (List.mem_map_of_mem hp)

theorem nestContKey_eq (hrec : RecEq rec₁ rec₂) (hpres : RecPres rec₂) {prog : List NestHole}
    {kb : Nat} {n : Name} {us : List Level} {ds : List Expr} {nPc : Nat} {cty : Expr}
    {st : NestState} (hpa : ProgActive prog st) :
    nestContKey ctx ops env rec₁ prog kb n us ds nPc cty st
      = nestContKey ctx ops env rec₂ prog kb n us ds nPc cty st := by
  unfold nestContKey
  split
  · rfl
  split
  · rfl
  · exact nestContNew_eq hrec hpres hpa

/-- **The older key step is the walk's** wherever the frame stack is in
progress: the frame-stack test is implied by `active`'s. -/
theorem nestContKeyP_eq (hrec : RecEq rec₁ rec₂) (hpres : RecPres rec₂) {prog : List NestHole}
    {kb : Nat} {n : Name} {us : List Level} {ds : List Expr} {nPc : Nat} {cty : Expr}
    {st : NestState} (hpa : ProgActive prog st) :
    nestContKeyP ctx ops env rec₁ prog kb n us ds nPc cty st
      = nestContKey ctx ops env rec₂ prog kb n us ds nPc cty st := by
  rw [← nestContKey_eq hrec hpres hpa]
  unfold nestContKeyP
  have hc : (prog.any (·.key == ⟨n, us, ds⟩) || st.active.contains ⟨n, us, ds⟩)
      = st.active.contains ⟨n, us, ds⟩ := by
    cases hA : st.active.contains ⟨n, us, ds⟩
    · rw [Bool.or_false, List.any_eq_false]
      intro h hh heq
      have := hpa h hh
      rw [beq_iff_eq.mp heq] at this
      simp [this] at hA
    · exact Bool.or_true _
  rw [hc]
  split
  · unfold nestContKey
    rw [if_pos ‹_›]
  · rfl

theorem nestContP_eq (hrec : RecEq rec₁ rec₂) (hpres : RecPres rec₂) {prog : List NestHole}
    {kb : Nat} {n : Name} {us : List Level} {args : List Expr} {st : NestState}
    (hpa : ProgActive prog st) :
    nestContP ctx ops env rec₁ prog kb n us args st = nestCont ctx ops env rec₂ prog kb n us args st := by
  simp only [nestContP, nestCont]
  have hpa' := hpa
  repeat' (first
    | rfl
    | exact nestContKeyP_eq hrec hpres hpa'
    | (refine bind_congr_ok fun _ _ => ?_)
    | split)

/-- **The older walk IS the walk** at every state whose frame stack is in
progress. -/
theorem nestPosP_eq : ∀ fuel prog dep kb e st, ProgActive prog st →
    nestPosP ops env ctx fuel prog dep kb e st = nestPos ops env ctx fuel prog dep kb e st
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, prog, dep, kb, e, st, hpa => by
    have ih : RecEq (nestPosP ops env ctx fuel) (nestPos ops env ctx fuel) := nestPosP_eq fuel
    -- the two recursive sites, at the entry's own frame stack and state
    have hpi : ∀ e', nestPosP ops env ctx fuel prog (dep + 1) (kb + 1) e' st
        = nestPos ops env ctx fuel prog (dep + 1) (kb + 1) e' st :=
      fun e' => ih prog (dep + 1) (kb + 1) e' st hpa
    have hc : ∀ n us args, nestContP ctx ops env (nestPosP ops env ctx fuel) prog kb n us args st
        = nestCont ctx ops env (nestPos ops env ctx fuel) prog kb n us args st :=
      fun _ _ _ => nestContP_eq ih (nestPos_active fuel) hpa
    simp only [nestPosP, nestPos, hpi, hc]
    -- the two sides differ only in their (definitionally equal) matchers
    rfl

/-- **At the walk's entries** (the empty frame stack, every state):
deleting the frame-stack test moved no verdict. -/
theorem nestPosP_eq_nil (fuel dep kb : Nat) (e : Expr) (st : NestState) :
    nestPosP ops env ctx fuel [] dep kb e st = nestPos ops env ctx fuel [] dep kb e st :=
  nestPosP_eq fuel [] dep kb e st fun _ h => nomatch h

end ConLeche
