module

public import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.NestContInv

public section

/-!
# The positivity walk's hook outputs

The walk calls its per-constructor hook (`NestHook`) at every walked
constructor and appends the hook's outputs to its state
(`NestState.done`); nothing else writes that field.  So every output a
successful run returns is an output of some hook run (`HookOut`), at
any operations and any hook: `checkBlockPositivity_done`.  The recursor
check reads its checked rules off these outputs
(`targetOutOf`, `RecCheckRun.lean`).
-/

namespace ConLeche

/-- **The hook accepted a walked constructor** (the table-free record of
a walked node, `FrameRec`). -/
@[expose] def HookOk (hook : NestHook CheckM) (e : NestCtorNf) : Prop :=
  ∃ xs, hook e = .ok xs

/-- **An output of a hook run.** -/
@[expose] def HookOut (hook : NestHook CheckM) (x : Nat × Nat × Expr) : Prop :=
  ∃ e xs, hook e = .ok xs ∧ x ∈ xs

/-- Every recorded output is a hook run's. -/
@[expose] def DoneOk (hook : NestHook CheckM) (st : NestState) : Prop :=
  ∀ x ∈ st.done.toList, HookOut hook x

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {hook : NestHook CheckM}

theorem DoneOk.empty : DoneOk hook {} := fun _ h => by simp at h

theorem DoneOk.push {st : NestState} (h : DoneOk hook st) {e : NestCtorNf}
    {xs : List (Nat × Nat × Expr)} (hx : hook e = .ok xs) :
    DoneOk hook { st with done := st.done ++ xs.toArray } := fun x hx' => by
  simp only [Array.toList_append, List.mem_append] at hx'
  rcases hx' with hx' | hx'
  · exact h x hx'
  · exact ⟨e, xs, hx, hx'⟩

theorem DoneOk.of_eq {st st' : NestState} (h : DoneOk hook st) (he : st'.done = st.done) :
    DoneOk hook st' := fun x hx => h x (he ▸ hx)

/-- A walk function keeps the recorded outputs hook runs'. -/
@[expose] def RunDone (hook : NestHook CheckM)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)) :
    Prop :=
  ∀ prog dep kb e st k nf st', rec prog dep kb e st = .ok (k, nf, st') → DoneOk hook st →
    DoneOk hook st'

theorem nestContainerC_done (st : NestState) (c : Name) :
    (nestContainerC ctx st c).2.done = st.done := by
  unfold nestContainerC; split <;> rfl

theorem nestGroupCtors_done {nPc : Nat} :
    ∀ (cs : List Name) (st : NestState) (ctors : List (ConstantVal × Nat)) (st' : NestState),
      nestGroupCtors (m := CheckM) ctx nPc cs st = .ok (ctors, st') → st'.done = st.done
  | [], st, ctors, st', h => by
    simp only [nestGroupCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; rfl
  | c :: cs, st, ctors, st', h => by
    simp only [nestGroupCtors, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i q hq
    obtain ⟨nP', L⟩ := q
    dsimp only at h
    split at h
    · split at h
      · simp at h
      rename_i r hr
      obtain ⟨rest, st₁⟩ := r
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [nestGroupCtors_done cs _ rest st₁ hr, nestContainerC_done]
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem nestAcceptGroup_done {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (grp : List (Name × Expr)) (st st' : NestState),
      nestAcceptGroup (m := CheckM) ctx hi us ds grp st = .ok st' → st'.done = st.done
  | [], st, st', h => by
    simp only [nestAcceptGroup, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | (c, ty) :: rest, st, st', h => by
    simp only [nestAcceptGroup, bind, Except.bind] at h
    split at h
    · split at h
      · simp at h
      have := nestAcceptGroup_done rest _ st' h
      exact this
    · exact nestAcceptGroup_done rest st st' h

section Rec

variable {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}

theorem nestFields_done (hrec : RunDone hook rec) {prog : List NestHole} {base : Nat}
    {err : CheckError} :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) (ks : List NestFieldKind)
      (nds : List (Expr × BinderMeta)) (res : Expr) (st' : NestState),
      nestFields rec prog base err nF j cur st = .ok (ks, nds, res, st') → DoneOk hook st →
      DoneOk hook st'
  | 0, _, _, st, _, _, _, st', h, hI => by
    simp only [nestFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, -, rfl⟩ := h
    exact hI
  | nF + 1, j, cur, st, ks, nds, res, st', h, hI => by
    unfold nestFields at h
    split at h
    · obtain ⟨⟨k₁, nd₁, st₁⟩, hr₁, h⟩ := exceptBind_ok h
      obtain ⟨⟨ks₂, nds₂, res₂, st₂⟩, hr₂, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, -, rfl⟩ := h
      exact nestFields_done hrec nF (j + 1) _ st₁ ks₂ nds₂ res₂ st₂ hr₂
        (hrec _ _ _ _ _ _ _ _ hr₁ hI)
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem nestCtors_done (hrec : RunDone hook rec) {prog : List NestHole} {hi : Nat}
    {us : List Level} {ds : List Expr} {nPc : Nat} {sub : Name → List Level → Option Expr} :
    ∀ (cs : List (ConstantVal × Nat)) (st st' : NestState),
      nestCtors ctx ops env hook rec prog hi us ds nPc sub cs st = .ok st' → DoneOk hook st →
      DoneOk hook st'
  | [], st, st', h, hI => by
    simp only [nestCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hI
  | (cv, nF) :: cs, st, st', h, hI => by
    simp only [nestCtors, bind, Except.bind] at h
    split at h
    · split at h
      · simp at h
      rename_i crest _
      split at h
      · simp at h
      split at h
      · simp at h
      split at h
      · simp at h
      rename_i r hr
      obtain ⟨ks, nds, cur, st₁⟩ := r
      have hI₁ := nestFields_done hrec nF 0 crest st ks nds cur st₁ hr hI
      dsimp only at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      split at h
      · split at h
        · simp at h
        rename_i xs hxs
        exact nestCtors_done hrec cs _ st' h (hI₁.push hxs)
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem nestFrame_done (hrec : RunDone hook rec) {prog : List NestHole} {hi : Nat}
    {us : List Level} {ds : List Expr} {nPc : Nat} {grp : List (Name × Expr)} {st st' : NestState}
    (h : nestFrame ctx ops env hook rec prog hi us ds nPc grp st = .ok st') (hI : DoneOk hook st) :
    DoneOk hook st' := by
  simp only [nestFrame, bind, Except.bind] at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i v hgc
  obtain ⟨ctors, st₁⟩ := v
  exact nestCtors_done hrec ctors st₁ st' h (hI.of_eq (nestGroupCtors_done _ st ctors st₁ hgc))

theorem nestContNew_done (hrec : RunDone hook rec) {prog : List NestHole} {kb : Nat} {n : Name}
    {us : List Level} {ds : List Expr} {nPc : Nat} {old : Option Nat} {st : NestState}
    {k : NestFieldKind} {st' : NestState}
    (h : nestContNew ctx ops env hook rec prog kb n us ds nPc old st = .ok (k, st'))
    (hI : DoneOk hook st) : DoneOk hook st' := by
  simp only [nestContNew, bind, Except.bind] at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i st₁ hfr
  have hI₁ := nestFrame_done hrec hfr (hI.of_eq rfl)
  split at h
  · simp at h
  rename_i st₂ hacc
  have hacc' := nestAcceptGroup_done _ _ st₂ hacc
  have hI₂ : DoneOk hook st₂ := hI₁.of_eq hacc'
  split at h <;>
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hI₂.of_eq rfl

theorem nestContKey_done (hrec : RunDone hook rec) {prog : List NestHole} {kb : Nat} {n : Name}
    {us : List Level} {ds : List Expr} {nPc : Nat} {st : NestState} {k : NestFieldKind}
    {st' : NestState}
    (h : nestContKey ctx ops env hook rec prog kb n us ds nPc st = .ok (k, st'))
    (hI : DoneOk hook st) : DoneOk hook st' := by
  unfold nestContKey at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact hI.of_eq rfl
      · exact nestContNew_done hrec h hI
    · exact nestContNew_done hrec h hI

theorem nestCont_done (hrec : RunDone hook rec) {prog : List NestHole} {kb : Nat} {n : Name}
    {us : List Level} {args : List Expr} {st : NestState} {k : NestFieldKind} {st' : NestState}
    (h : nestCont ctx ops env hook rec prog kb n us args st = .ok (k, st'))
    (hI : DoneOk hook st) : DoneOk hook st' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hkey⟩ := nestCont_inv h
  exact nestContKey_done hrec hkey (hI.of_eq (nestContainerC_done st n))

end Rec

theorem nestPos_done : ∀ fuel, RunDone hook (nestPos ops env ctx hook fuel)
  | 0 => by
    intro prog dep kb e st k nf st' h _
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1 => by
    intro prog dep kb e st k nf st' h hI
    rw [nestPos] at h
    cases hw : ops.whnf env dep e with
    | error err => simp [hw, bind, Except.bind] at h
    | ok w =>
      simp only [hw, bind, Except.bind] at h
      by_cases hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false
      · rw [if_pos (by simpa using hocc)] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        exact hI
      rw [if_neg (by simpa using hocc)] at h
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        split at h
        · simp at h
        rename_i v hv
        obtain ⟨k₁, nb, st₁⟩ := v
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        exact nestPos_done fuel _ _ _ _ _ _ _ _ hv hI
      · split at h
        · repeat' split at h
          all_goals first
            | (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
               obtain ⟨-, -, rfl⟩ := h
               exact hI)
            | simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          split at h
          · simp at h
          rename_i v hv
          obtain ⟨k₁, st₁⟩ := v
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, -, rfl⟩ := h
          exact nestCont_done (nestPos_done fuel) hv hI
        · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem nestMemberCtor_done {nF : Nat} {crest : Expr} {st : NestState}
    {ks : List NestFieldKind} {tyN : Expr} {st' : NestState}
    (h : nestMemberCtor ops env ctx hook nF crest st = .ok (ks, tyN, st')) (hI : DoneOk hook st) :
    DoneOk hook st' := by
  unfold nestMemberCtor at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨ks₁, nds₁, res, st₁⟩ := r
  simp only at h
  have hI₁ := nestFields_done (nestPos_done _) nF 0 crest st ks₁ nds₁ res st₁ hr hI
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact hI₁
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem nestSeeds_done :
    ∀ (ks : List (NestKey × Nat)) (st st' : NestState), nestSeeds ops env ctx hook ks st = .ok st' →
      DoneOk hook st → DoneOk hook st'
  | [], st, st', h, hI => by
    simp only [nestSeeds, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hI
  | (key, nPc) :: ks, st, st', h, hI => by
    simp only [nestSeeds, bind, Except.bind] at h
    split at h
    rotate_left
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨k₁, st₁⟩ := r
    exact nestSeeds_done ks st₁ st' h (nestContKey_done (nestPos_done _) hr hI)

/-- **Every output of the install's walk is a hook run's.** -/
theorem checkBlockPositivity_done {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {keys : List NestKey}
    {done : List (Nat × Nat × Expr)}
    (h : checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs hook
      = .ok (kinds, nfs, keys, done)) :
    ∀ x ∈ done, HookOut hook x := by
  obtain ⟨cvTa0, fvsP, rest, holes, -, -, -, hthr⟩ := checkBlockPositivity_inv_I h
  obtain ⟨stM, seeds, stF, hM, -, hstF, -, hdone, -⟩ := hthr (DoneOk hook) (fun _ _ => True)
    DoneOk.empty (fun _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI hm hx => ⟨(nestMemberCtor_done hm hI).push hx, trivial⟩)
  intro x hx
  rw [hdone] at hx
  exact nestSeeds_done seeds stM stF hstF hM x hx

end ConLeche
