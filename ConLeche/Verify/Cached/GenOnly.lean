module

public import ConLeche.Cached.Installed

/-!
# The generate-only install of an inductive block is the checked one's generator (task #410)

The block install is its generator with its checks marked: every part
whose only output is a verdict runs through a runner `ck`
(`ConLeche/Cached/CheckerC.lean`).  The checked install runs each check
in a memo of its own (`isoC`: from the fresh state, the caller's state
handed on); the generate-only install skips it (`ckC false`).  So the
generator never sees whether a check ran, and an accepting checked run
is, step for step, the generate-only run from the same state:

* `GenRun x₁ x₂` — every accepting run of `x₁` is a run of `x₂` from
  the same state, with the same value and the same final state;
* `GenRun.ckC` — the two runners are so related on every check;
* bottom-up through the install code, every stage written over a
  runner is so related at the two runners (`…_gen`), up to
  `checkIndDeclC_gen` (the block install) and `genIndStep_eq` (the
  fold's step: where `installDeclStep` accepts an inductive block,
  `genIndStep` returns the index that step pushed).

Nothing here reads the environment's well-formedness or the memo's
invariant: the relation is the install code's own structure.  The
theorem holds at every index, a module's exported view included.
-/

public section

namespace ConLeche.Cached

open ConLeche

/-! ## The relation -/

/-- **`x₂` reproduces every accepting run of `x₁`**: from the same state,
the same value and the same final state. -/
structure GenRun {α : Type} (x₁ x₂ : CheckCM α) : Prop where
  run : ∀ s a s', x₁ s = .ok (a, s') → x₂ s = .ok (a, s')

theorem GenRun.refl {α : Type} {x : CheckCM α} : GenRun x x := ⟨fun _ _ _ h => h⟩

theorem GenRun.bind {α β : Type} {x₁ x₂ : CheckCM α} {k₁ k₂ : α → CheckCM β}
    (hx : GenRun x₁ x₂) (hk : ∀ a, GenRun (k₁ a) (k₂ a)) : GenRun (x₁ >>= k₁) (x₂ >>= k₂) := by
  refine ⟨fun s b s' h => ?_⟩
  have h₁ : (x₁ >>= k₁) s = (x₁ s).bind (fun v => k₁ v.1 v.2) := rfl
  have h₂ : (x₂ >>= k₂) s = (x₂ s).bind (fun v => k₂ v.1 v.2) := rfl
  rw [h₁] at h
  rw [h₂]
  cases hx₁ : x₁ s with
  | error e => rw [hx₁] at h; cases h
  | ok v =>
    rw [hx₁] at h
    rw [hx.run s v.1 v.2 hx₁]
    exact (hk v.1).run v.2 b s' h

theorem GenRun.bind_same {α β : Type} {x : CheckCM α} {k₁ k₂ : α → CheckCM β}
    (hk : ∀ a, GenRun (k₁ a) (k₂ a)) : GenRun (x >>= k₁) (x >>= k₂) :=
  GenRun.bind GenRun.refl hk

theorem GenRun.ite {α : Type} {c : Prop} {d : Decidable c} {t₁ t₂ e₁ e₂ : CheckCM α}
    (ht : c → GenRun t₁ t₂) (he : ¬c → GenRun e₁ e₂) :
    GenRun (@ite _ c d t₁ e₁) (@ite _ c d t₂ e₂) := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]; exact ht h
  · rw [ite_eq_right h, ite_eq_right h]; exact he h

/-- **The two runners**: a check in a memo of its own that accepts hands
on the caller's state, as the skipped check does. -/
theorem GenRun.ckC (c : CheckCM Unit) : GenRun (ckC true c) (ckC false c) := by
  refine ⟨fun s a s' h => ?_⟩
  show (pure () : CheckCM Unit) s = _
  simp only [ConLeche.Cached.ckC, isoC] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · cases h

/-! ## The stages, bottom-up -/

section Stages

variable {ops : CheckerOps CheckCM}

theorem checkBlockTeleF_gen (fe : FEnv) (nP : Nat) (ms : MemberShape) :
    GenRun (checkBlockTeleF (ckC true) ops fe nP ms)
      (checkBlockTeleF (ckC false) ops fe nP ms) := by
  unfold checkBlockTeleF
  repeat' (first
    | with_reducible exact GenRun.refl
    | with_reducible exact GenRun.ckC _
    | ((with_reducible apply GenRun.bind (GenRun.ckC _)); intro)
    | ((with_reducible apply GenRun.bind_same); intro)
    | ((with_reducible apply GenRun.ite) <;> intro)
    | split)

theorem checkBlockTelesF_gen (fe : FEnv) (nP : Nat) :
    ∀ mss, GenRun (checkBlockTelesF (ckC true) ops fe nP mss)
      (checkBlockTelesF (ckC false) ops fe nP mss)
  | [] => GenRun.refl
  | ms :: rest => by
    unfold checkBlockTelesF
    exact GenRun.bind (checkBlockTeleF_gen fe nP ms) fun _ =>
      GenRun.bind (checkBlockTelesF_gen fe nP rest) fun _ => GenRun.refl

theorem checkBlockIndsF_gen (fe : FEnv) (p : BlockParts) (isRec : Bool) :
    GenRun (checkBlockIndsF (ckC true) ops fe p isRec)
      (checkBlockIndsF (ckC false) ops fe p isRec) := by
  unfold checkBlockIndsF
  split
  · exact GenRun.refl
  · exact GenRun.bind (checkBlockTeleF_gen fe _ _) fun _ =>
      GenRun.bind (checkBlockTelesF_gen fe _ _) fun _ =>
        GenRun.bind (GenRun.ckC _) fun _ => GenRun.refl

theorem checkSumCtorF_gen (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat)
    (cvTa : ConstantVal) :
    GenRun (checkSumCtorF (ckC true) ops fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa)
      (checkSumCtorF (ckC false) ops fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa) := by
  unfold checkSumCtorF
  repeat' (first
    | with_reducible exact GenRun.refl
    | with_reducible exact GenRun.ckC _
    | ((with_reducible apply GenRun.bind (GenRun.ckC _)); intro)
    | ((with_reducible apply GenRun.bind_same); intro)
    | ((with_reducible apply GenRun.ite) <;> intro)
    | split)

theorem checkSumCtorsF_gen (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvTa : ConstantVal) :
    ∀ cs, GenRun (checkSumCtorsF (ckC true) ops fe₀ fe T lps nP nIdx resSort isProp large cvTa cs)
      (checkSumCtorsF (ckC false) ops fe₀ fe T lps nP nIdx resSort isProp large cvTa cs)
  | [] => GenRun.refl
  | c :: cs => by
    unfold checkSumCtorsF
    exact GenRun.bind (checkSumCtorF_gen ..) fun _ =>
      GenRun.bind (checkSumCtorsF_gen fe₀ fe T lps nP nIdx resSort isProp large cvTa cs)
        fun _ => GenRun.refl

theorem checkBlockCtorsF_gen (fe₀ fe : FEnv) (p : BlockShape) :
    ∀ l, GenRun (checkBlockCtorsF (ckC true) ops fe₀ fe p l)
      (checkBlockCtorsF (ckC false) ops fe₀ fe p l)
  | [] => GenRun.refl
  | (ms, cvTa) :: rest => by
    unfold checkBlockCtorsF
    exact GenRun.bind (checkSumCtorsF_gen ..) fun _ =>
      GenRun.bind (checkBlockCtorsF_gen fe₀ fe p rest) fun _ => GenRun.refl

theorem classStreamRecs_gen (fe : FEnv) :
    ∀ recs, GenRun (classStreamRecs (ckC true) ops fe recs)
      (classStreamRecs (ckC false) ops fe recs)
  | [] => GenRun.refl
  | rc :: rcs => by
    unfold classStreamRecs
    exact GenRun.bind (GenRun.ckC _) fun _ =>
      GenRun.bind (classStreamRecs_gen fe rcs) fun _ => GenRun.refl

theorem classRecTyOk_gen (fe : FEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (cvRi : ConstantVal) (c : Nat) :
    GenRun (classRecTyOk (ckC true) ops fe g k rc cvRi c)
      (classRecTyOk (ckC false) ops fe g k rc cvRi c) := by
  unfold classRecTyOk
  repeat' (first
    | with_reducible exact GenRun.refl
    | with_reducible exact GenRun.ckC _
    | ((with_reducible apply GenRun.bind (GenRun.ckC _)); intro)
    | ((with_reducible apply GenRun.bind_same); intro)
    | ((with_reducible apply GenRun.ite) <;> intro)
    | split)

theorem classRecTysOk_gen (fe : FEnv) (g : ClassGen) (k : Nat) :
    ∀ rcs cvs cs, GenRun (classRecTysOk (ckC true) ops fe g k rcs cvs cs)
      (classRecTysOk (ckC false) ops fe g k rcs cvs cs)
  | rc :: rcs, cvRi :: cvs, c :: cs => by
    unfold classRecTysOk
    exact GenRun.bind (classRecTyOk_gen ..) fun _ =>
      GenRun.bind (classRecTysOk_gen fe g k rcs cvs cs) fun _ => GenRun.refl
  | [], _, _ => by unfold classRecTysOk; exact GenRun.refl
  | _ :: _, [], _ => by unfold classRecTysOk; exact GenRun.refl
  | _ :: _, _ :: _, [] => by unfold classRecTysOk; exact GenRun.refl

theorem classRuleOk_gen (w : StructWalkers) (feT feR : FEnv) (cvR : ConstantVal) (n : Nat)
    (gen : Expr) :
    GenRun (classRuleOk (ckC true) ops w feT feR cvR n gen)
      (classRuleOk (ckC false) ops w feT feR cvR n gen) := by
  unfold classRuleOk
  exact GenRun.bind (GenRun.ckC _) fun _ => GenRun.refl

theorem classRulesOk_gen (w : StructWalkers) (feT feR : FEnv) (g : ClassGen)
    (recOf : Nat → Option Name) (cvR : ConstantVal) (c : Nat) :
    ∀ xs, GenRun (classRulesOk (ckC true) ops w feT feR g recOf cvR c xs)
      (classRulesOk (ckC false) ops w feT feR g recOf cvR c xs)
  | [] => GenRun.refl
  | x :: xs => by
    unfold classRulesOk
    exact GenRun.bind_same fun _ => GenRun.bind (classRuleOk_gen ..) fun _ =>
      GenRun.bind (classRulesOk_gen w feT feR g recOf cvR c xs) fun _ => GenRun.refl

theorem classRecsRulesOk_gen (w : StructWalkers) (feT feR : FEnv) (g : ClassGen)
    (recOf : Nat → Option Name) :
    ∀ cvs cs, GenRun (classRecsRulesOk (ckC true) ops w feT feR g recOf cvs cs)
      (classRecsRulesOk (ckC false) ops w feT feR g recOf cvs cs)
  | cvG :: cvs, c :: cs => by
    unfold classRecsRulesOk
    exact GenRun.bind (classRulesOk_gen ..) fun _ =>
      GenRun.bind (classRecsRulesOk_gen w feT feR g recOf cvs cs) fun _ => GenRun.refl
  | [], _ => by unfold classRecsRulesOk; exact GenRun.refl
  | _ :: _, [] => by unfold classRecsRulesOk; exact GenRun.refl

end Stages

/-! ## The block install -/

variable (mode : CheckMode)

theorem genRecCheck_gen (fe : FEnv) (p : BlockShape) (nestedBit : Bool) (params : List Expr)
    (tbl : List NestCtorNf) (rd : ClassRead) (Ms : List TargetMajor) (cvTas : List ConstantVal)
    (block : List ConstantInfo) :
    GenRun (genRecCheck (shadowOpsC mode true) fe p nestedBit params tbl rd Ms cvTas block)
      (genRecCheck (shadowOpsC mode false) fe p nestedBit params tbl rd Ms cvTas block) := by
  unfold genRecCheck
  dsimp only [shadowOpsC]
  repeat' (first
    | with_reducible exact GenRun.refl
    | ((apply GenRun.bind (classStreamRecs_gen _ _)); intro)
    | ((apply GenRun.bind (classRecTysOk_gen ..)); intro)
    | ((apply GenRun.bind (classRecsRulesOk_gen ..)); intro)
    | ((with_reducible apply GenRun.bind_same); intro)
    | ((with_reducible apply GenRun.ite) <;> intro)
    | split)

theorem checkBlockPassS_gen (fe : FEnv) (p₀ : BlockParts) (isRec : Bool) :
    GenRun (checkBlockPassS mode fe p₀ isRec true) (checkBlockPassS mode fe p₀ isRec false) := by
  unfold checkBlockPassS
  exact GenRun.bind (checkBlockIndsF_gen ..) fun _ => GenRun.bind_same fun _ =>
    GenRun.bind (checkBlockCtorsF_gen ..) fun _ => GenRun.refl

theorem checkBlockTailS_gen (block : List ConstantInfo) (q : BlockPass FEnv) :
    GenRun (checkBlockTailS mode block q true) (checkBlockTailS mode block q false) := by
  unfold checkBlockTailS
  exact GenRun.bind_same fun _ => GenRun.bind_same fun _ =>
    GenRun.bind (genRecCheck_gen ..) fun _ => GenRun.refl

theorem checkBlockKS_gen (fe : FEnv) (block : List ConstantInfo) (p₀ : BlockParts) :
    GenRun (checkBlockKS mode fe block p₀ true) (checkBlockKS mode fe block p₀ false) := by
  unfold checkBlockKS
  repeat' (first
    | with_reducible exact GenRun.refl
    | exact GenRun.bind (checkBlockPassS_gen ..) fun _ => checkBlockTailS_gen ..
    | ((with_reducible apply GenRun.bind_same); intro)
    | ((with_reducible apply GenRun.ite) <;> intro)
    | split)

/-- **The block install**: an accepting checked install is the
generate-only install's run, from the same state to the same index and
state. -/
theorem checkIndDeclC_gen (fe : FEnv) (block : List ConstantInfo) (nP : Nat) :
    GenRun (checkIndDeclC mode fe block nP true) (checkIndDeclC mode fe block nP false) := by
  unfold checkIndDeclC
  split
  · exact GenRun.refl
  · split
    · split
      · exact checkBlockKS_gen ..
      · exact GenRun.refl
    · exact GenRun.refl

/-- **The fold's step on an inductive block, generate-only** (the
contract of `genIndStep`): where the checked step `installDeclStep`
accepts the block at an index, the generate-only step at that index
returns the index the checked step pushed (and the checked step records
no pending check). -/
theorem genIndStep_eq {pins : List NatOpPinSet} {i : Nat} {fe : FEnv}
    {pend : Array PendingCheck} {block : List ConstantInfo} {nP : Nat}
    {q : Nat × FEnv × Array PendingCheck}
    (h : installDeclStep mode pins (i, fe, pend) (.indDecl block nP) = .ok q) :
    q.2.2 = pend ∧ genIndStep mode fe block nP = .ok q.2.1 := by
  obtain ⟨fe', pend', s', rfl, hst⟩ := installDeclStep_ok h
  -- the step body on a block: the flush, then the block install, the
  -- pending checks handed on
  have key : installStepC mode pins i fe pend (.indDecl block nP) =
      (flushC >>= fun _ => checkIndDeclC mode fe block nP true) >>= fun x => pure (x, pend) :=
    rfl
  rw [key] at hst
  have hb : (flushC >>= fun _ => checkIndDeclC mode fe block nP true : CheckCM FEnv) {} =
      .ok (fe', s') ∧ pend' = pend := by
    have hs : ((flushC >>= fun _ => checkIndDeclC mode fe block nP true) >>=
        fun x => (pure (x, pend) : CheckCM (FEnv × Array PendingCheck))) {} =
        ((flushC >>= fun _ => checkIndDeclC mode fe block nP true : CheckCM FEnv) {}).bind
          (fun v => .ok ((v.1, pend), v.2)) := rfl
    rw [hs] at hst
    cases hr : (flushC >>= fun _ => checkIndDeclC mode fe block nP true : CheckCM FEnv) {} with
    | error e => rw [hr] at hst; cases hst
    | ok v =>
      rw [hr] at hst
      simp only [Except.bind, Except.ok.injEq, Prod.mk.injEq] at hst
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hst
      exact ⟨rfl, rfl⟩
  obtain ⟨hb, rfl⟩ := hb
  refine ⟨rfl, ?_⟩
  have hg := (GenRun.bind_same (x := (flushC : CheckCM Unit))
    (fun _ => checkIndDeclC_gen mode fe block nP)).run {} fe' s' hb
  unfold genIndStep genIndDeclC
  show (match (flushC >>= fun _ => checkIndDeclC mode fe block nP false : CheckCM FEnv) {} with
    | .ok (fe', _) => Except.ok fe'
    | .error e => .error e) = _
  rw [hg]

end ConLeche.Cached
