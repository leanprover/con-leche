module

public import ConLeche.Verify.Cached.NestPosC
import ConLeche.Verify.Cached.BridgeCS2
import ConLeche.Verify.Cached.SimCS
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Abstract
public section

/-!
# The home table at the cached driver

The positivity stage computes the home table (`homeTableAt`,
`Kernel/Inductives/RecHome.lean`) at the walk's operations; the cached
driver runs it at the shared operations.  The simulation needs every
`whnf` input well scoped at its depth: a member constructor's crest as
the walk's, a container constructor's at a key below the members' holes
— the key is a leaf's parameters, checked below `hiAt 0` by the table
(`homeLeafNew`) and well scoped at SOME depth because every normal form
the table records is (`LeavesScoped`).
-/

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode} {env : Env}

/-! ## Well-scoped leaves -/

/-- A term below its `Π` binders is well scoped where the term is. -/
theorem WScoped.piLeaf : ∀ {e : Expr} {d : Nat}, WScoped d e → WScoped d e.piLeaf
  | .forallE ty body bm, d, h => by
    simp only [WScoped] at h
    exact WScoped.piLeaf (e := body) h.2
  | .bvar _, _, h | .fvar _ _, _, h | .sort _, _, h | .const _ _, _, h | .app _ _, _, h
  | .lam _ _ _, _, h | .letE _ _ _, _, h | .lit _, _, h | .proj _ _ _, _, h => h

/-- An application's arguments are well scoped where it is. -/
theorem WScoped.getAppArgs : ∀ {e : Expr} {d : Nat}, WScoped d e → ∀ x ∈ e.getAppArgs, WScoped d x
  | .app f a, d, h, x, hx => by
    simp only [WScoped] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact WScoped.getAppArgs h.1 x hx
    · exact h.2
  | .bvar _, _, _, x, hx | .fvar _ _, _, _, x, hx | .sort _, _, _, x, hx
  | .const _ _, _, _, x, hx | .lam _ _ _, _, _, x, hx | .forallE _ _ _, _, _, x, hx
  | .letE _ _ _, _, _, x, hx | .lit _, _, _, x, hx | .proj _ _ _, _, _, x, hx => by
    simp [Expr.getAppArgs] at hx

/-- Every recorded leaf is well scoped at some depth. -/
@[expose] def LeavesScoped (n : NestClassCtorNf) : Prop :=
  ∀ l, some l ∈ n.leaves → ∃ D, WScoped D l

/-- Every recorded constructor of an entry has well-scoped leaves. -/
@[expose] def EntryScoped (e : HomeEntry) : Prop := ∀ n ∈ e.nfs, LeavesScoped n

theorem leavesScoped_of {ctx : NestCtx} {prog : List NestHole} {hi : Nat} {us : List Level}
    {ds : List Expr} {cv : ConstantVal} {nds : List (Expr × BinderMeta)} {cur : Expr}
    (h : ∀ nd ∈ nds, ∃ D, WScoped D nd.1) :
    LeavesScoped (nestClassCtorNfOf ctx prog hi us ds cv nds cur) := by
  intro l hl
  simp only [nestClassCtorNfOf, List.mem_map] at hl
  obtain ⟨nd, hnd, hl⟩ := hl
  split at hl
  · obtain ⟨D, hD⟩ := h nd hnd
    exact ⟨D, Option.some.inj hl ▸ WScoped.piLeaf hD⟩
  · exact nomatch hl

/-! ## The normal forms -/

theorem nestNfS_simW (hμ : mode.verifiedChecks = true) (henv : EnvWF env) (names : List Name)
    (nP hi : Nat) :
    ∀ (fuel dep : Nat) {e : Expr} {s₀ : CState}, WScoped dep e → CSOK mode env s₀ →
      SimC mode env s₀ (fun v w => v = w ∧ WScoped dep v)
        (nestNf (sharedOpsC mode (mkFEnv env)) env names nP hi fuel dep e)
        (nestNf (fueledOpsM mode) env names nP hi fuel dep e)
  | 0, _, _, _, _, _ => SimC.throw
  | fuel + 1, dep, e, s₀, hw, hs => by
    rw [nestNf, nestNf]
    dsimp only [sharedOpsC]
    refine SimC.bind (opE_whnf_sim hμ henv hs hw) (fun s₁ w w' hs₁ hW => ?_)
    obtain ⟨rfl, hww⟩ := hW
    unfold nestNfAt
    split
    · exact SimC.pure hs₁ ⟨rfl, by split <;> assumption⟩
    · split
      · rename_i a b bm
        simp only [WScoped] at hww
        refine SimC.bind (nestNfS_simW hμ henv names nP hi fuel (dep + 1)
          (WScoped.instantiate1 hww.1 0 hww.2) hs₁) (fun s₂ nb nb' hs₂ hB => ?_)
        obtain ⟨rfl, hnb⟩ := hB
        exact SimC.pure hs₂ ⟨rfl, by simp only [WScoped]; exact ⟨hww.1, WScoped.abstract1 0 hnb⟩⟩
      · exact SimC.pure hs₁ ⟨rfl, hww⟩

theorem nestTeleNfS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) (names : List Name)
    (nP hi fuel base : Nat) :
    ∀ (nF j : Nat) {cur : Expr} {s₀ : CState}, WScoped (base + j) cur → CSOK mode env s₀ →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ nd ∈ v.1, ∃ D, WScoped D nd.1)
        (nestTeleNf (sharedOpsC mode (mkFEnv env)) env names nP hi fuel base nF j cur)
        (nestTeleNf (fueledOpsM mode) env names nP hi fuel base nF j cur)
  | 0, _, _, _, _, hs => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | nF + 1, j, cur, s₀, hw, hs => by
    cases cur
    case forallE a b bm =>
      simp only [nestTeleNf]
      simp only [WScoped] at hw
      refine SimC.bind (nestNfS_simW hμ henv names nP hi fuel (base + j) hw.1 hs)
        (fun s₁ nd nd' hs₁ hN => ?_)
      obtain ⟨rfl, hnd⟩ := hN
      refine SimC.bind (nestTeleNfS_sim hμ henv names nP hi fuel base nF (j + 1)
        (by rw [← Nat.add_assoc]; exact WScoped.instantiate1 hw.1 0 hw.2) hs₁)
        (fun s₂ r r' hs₂ hR => ?_)
      obtain ⟨rfl, hr⟩ := hR
      rcases r with ⟨nds, res⟩
      refine SimC.pure hs₂ ⟨rfl, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, hnd⟩
      · exact hr x hx
    all_goals exact SimC.throw

theorem nestMemberCtorNfS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {ctx : NestCtx} {holes : List Expr}
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) {cv : ConstantVal} (nF : Nat)
    (hcv : cv.type.hasFvar = false) {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ LeavesScoped v)
      (nestMemberCtorNf (sharedOpsC mode (mkFEnv env)) env ctx holes cv nF)
      (nestMemberCtorNf (fueledOpsM mode) env ctx holes cv nF) := by
  unfold nestMemberCtorNf
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ crest crest' hs₁ hP => ?_)
  obtain ⟨rfl, hcr⟩ := hP
  refine SimC.bind (nestTeleNfS_sim hμ henv _ _ _ _ _ nF 0
    (by simpa using memberCrest_wscoped hholes hpar hcv hcr) hs₁) (fun s₂ r r' hs₂ hR => ?_)
  obtain ⟨rfl, hr⟩ := hR
  rcases r with ⟨nds, cur⟩
  exact SimC.pure hs₂ ⟨rfl, leavesScoped_of hr⟩

theorem nestClassGroupS_sim {ctx : NestCtx} (hc : NestCtxOk ctx) (I : Name) (us : List Level)
    (ds : List Expr) {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ ∀ x ∈ v, x.2.hasFvar = false)
      (nestClassGroup (m := CheckCM) ctx I us ds) (nestClassGroup (m := FueledM) ctx I us ds) := by
  unfold nestClassGroup
  refine SimC.bind (nestInstTypeS_sim hc hs _ _) (fun s₁ q q' hs₁ hQ => ?_)
  obtain ⟨rfl, hq⟩ := hQ
  exact nestGrowGroupS_sim hc _ us ds _ _ hs₁ (fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact hq)

theorem nestFrameCtorNfS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {ctx : NestCtx} {us : List Level} {ds : List Expr} (hds : ∀ x ∈ ds, WScoped (ctx.hiAt 0) x)
    {grp : List (Name × Expr)} (hg : ∀ x ∈ grp, x.2.hasFvar = false) {cv : ConstantVal}
    (nF : Nat) (hcv : cv.type.hasFvar = false) {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ LeavesScoped v)
      (nestFrameCtorNf (sharedOpsC mode (mkFEnv env)) env ctx us ds grp cv nF)
      (nestFrameCtorNf (fueledOpsM mode) env ctx us ds grp cv nF) := by
  unfold nestFrameCtorNf
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ crest crest' hs₁ hP => ?_)
  obtain ⟨rfl, hcr⟩ := hP
  have hwc : WScoped (ctx.hiAt 0 + grp.length) crest := by
    refine wscoped_instPisWith (fun x hx => WScoped.mono (Nat.le_add_right _ _) (hds x hx))
      (WScoped.replaceConsts_closed (fun c us' e he => ?_) _
        (by rw [Expr.hasFvar_instantiateLevelParams]; exact hcv)) hcr
    unfold grpSub at he
    split at he
    · exact frameHoles_wscoped hg _ he
    · exact nomatch he
  refine SimC.bind (nestTeleNfS_sim hμ henv _ _ _ _ _ nF 0 (by simpa using hwc) hs₁)
    (fun s₂ r r' hs₂ hR => ?_)
  obtain ⟨rfl, hr⟩ := hR
  rcases r with ⟨nds, cur⟩
  exact SimC.pure hs₂ ⟨rfl, leavesScoped_of hr⟩

/-! ## The table -/

theorem mapM_loopS_sim {α β : Type} {f : α → CheckCM β} {g : α → FueledM β} {Q : β → Prop}
    (hf : ∀ a {s : CState}, CSOK mode env s → SimC mode env s (fun v w => v = w ∧ Q v) (f a) (g a)) :
    ∀ (l : List α) (acc : List β) {s₀ : CState}, CSOK mode env s₀ → (∀ x ∈ acc, Q x) →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ x ∈ v, Q x)
        (List.mapM.loop f l acc) (List.mapM.loop g l acc)
  | [], acc, _, hs, hacc => by
    unfold List.mapM.loop
    exact SimC.pure hs ⟨rfl, fun x hx => hacc x (List.mem_reverse.mp hx)⟩
  | a :: l, acc, _, hs, hacc => by
    unfold List.mapM.loop
    refine SimC.bind (hf a hs) (fun s₁ b b' hs₁ hB => ?_)
    obtain ⟨rfl, hb⟩ := hB
    exact mapM_loopS_sim hf l (b :: acc) hs₁ (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb
      · exact hacc x hx)

theorem mapMS_sim {α β : Type} {f : α → CheckCM β} {g : α → FueledM β} {Q : β → Prop}
    (l : List α)
    (hf : ∀ a ∈ l, ∀ {s : CState}, CSOK mode env s →
      SimC mode env s (fun v w => v = w ∧ Q v) (f a) (g a)) {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ ∀ x ∈ v, Q x) (l.mapM f) (l.mapM g) := by
  -- restrict the functions to the list's elements
  have key : ∀ (l' : List α), (∀ a ∈ l', a ∈ l) → ∀ (acc : List β) {s₀ : CState},
      CSOK mode env s₀ → (∀ x ∈ acc, Q x) →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ x ∈ v, Q x)
        (List.mapM.loop f l' acc) (List.mapM.loop g l' acc) := by
    intro l' hl'
    induction l' with
    | nil =>
      intro acc s₀ hs hacc
      unfold List.mapM.loop
      exact SimC.pure hs ⟨rfl, fun x hx => hacc x (List.mem_reverse.mp hx)⟩
    | cons a l' ih =>
      intro acc s₀ hs hacc
      unfold List.mapM.loop
      refine SimC.bind (hf a (hl' a List.mem_cons_self) hs) (fun s₁ b b' hs₁ hB => ?_)
      obtain ⟨rfl, hb⟩ := hB
      exact ih (fun x hx => hl' x (List.mem_cons_of_mem _ hx)) (b :: acc) hs₁ (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hb
        · exact hacc x hx)
  exact key l (fun _ h => h) [] hs (fun _ h => nomatch h)

theorem homeEntryNfsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {ctx : NestCtx} (hc : NestCtxOk ctx) {holes : List Expr}
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) (I : Name) (us : List Level)
    {ctors : List (ConstantVal × Nat)} (hcl : ∀ c ∈ ctors, c.1.type.hasFvar = false)
    {key : Option (List Expr)} (hkey : ∀ ds, key = some ds → ∀ x ∈ ds, WScoped (ctx.hiAt 0) x)
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ ∀ n ∈ v, LeavesScoped n)
      (homeEntryNfs (sharedOpsC mode (mkFEnv env)) env ctx holes I us ctors key)
      (homeEntryNfs (fueledOpsM mode) env ctx holes I us ctors key) := by
  cases key with
  | none =>
    unfold homeEntryNfs
    exact mapMS_sim ctors (fun c hc' s hs' =>
      nestMemberCtorNfS_sim hμ henv hholes hpar c.2 (hcl c hc') hs') hs
  | some ds =>
    unfold homeEntryNfs
    refine SimC.bind (nestClassGroupS_sim hc I us ds hs) (fun s₁ grp grp' hs₁ hG => ?_)
    obtain ⟨rfl, hg⟩ := hG
    exact mapMS_sim ctors (fun c hc' s hs' =>
      nestFrameCtorNfS_sim hμ henv (hkey ds rfl) hg c.2 (hcl c hc') hs') hs₁

theorem homeMembersS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {ctx : NestCtx} (hc : NestCtxOk ctx) {holes : List Expr}
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x)
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hcl : ∀ cs ∈ ctorsAs, ∀ c ∈ cs, c.1.type.hasFvar = false) {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ ∀ e ∈ v, EntryScoped e)
      (homeMembers (sharedOpsC mode (mkFEnv env)) env ctx holes ctorsAs)
      (homeMembers (fueledOpsM mode) env ctx holes ctorsAs) := by
  unfold homeMembers
  refine mapMS_sim _ (fun t _ s hs' => ?_) hs
  have hclt : ∀ c ∈ ctorsAs.getD t [], c.1.type.hasFvar = false := by
    intro c hc'
    rw [List.getD_eq_getElem?_getD] at hc'
    cases h : ctorsAs[t]? with
    | none => rw [h] at hc'; exact nomatch hc'
    | some cs => rw [h] at hc'; exact hcl cs (List.mem_of_getElem? h) c hc'
  refine SimC.bind (homeEntryNfsS_sim hμ henv hc hholes hpar _ _ hclt (key := none)
    (fun _ h => nomatch h) hs') (fun s₁ nfs nfs' hs₁ hN => ?_)
  obtain ⟨rfl, hn⟩ := hN
  exact SimC.pure hs₁ ⟨rfl, hn⟩

/-- The instances the table follows: parameters below the members' holes,
closed constructor types. -/
theorem homeNews_ok {ctx : NestCtx} (hc : NestCtxOk ctx) {T : List HomeEntry}
    (hT : ∀ e ∈ T, EntryScoped e) :
    ∀ q ∈ homeNews ctx T, (∀ x ∈ q.2.2.1, WScoped (ctx.hiAt 0) x) ∧
      ∀ c ∈ q.2.2.2.2, c.1.type.hasFvar = false := by
  intro q hq
  simp only [homeNews, List.mem_flatMap] at hq
  obtain ⟨e, he, hq⟩ := hq
  split at hq
  · simp only [List.mem_flatMap, List.mem_filterMap] at hq
    obtain ⟨n, hn, l?, hl, hq⟩ := hq
    cases l? with
    | none => exact nomatch hq
    | some l =>
      obtain ⟨D, hD⟩ := hT e he n hn l hl
      simp only [Option.bind_some] at hq
      unfold homeLeafNew at hq
      split at hq
      · rename_i I us hfn
        split at hq
        · exact nomatch hq
        · split at hq
          · rename_i nPc ctors hcont
            dsimp only at hq
            split at hq
            · rename_i hck
              obtain rfl := Option.some.inj hq
              refine ⟨fun x hx => ?_, nestContainer_closed hc hcont⟩
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
                at hck
              have h1 := hck.2 x hx
              exact WScoped.of_fvarsBelow (WScoped.getAppArgs hD x (List.mem_of_mem_take hx))
                (fvarB_le h1.2)
            · exact nomatch hq
          · exact nomatch hq
      · exact nomatch hq
  · exact nomatch hq

theorem homeAddS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {ctx : NestCtx} (hc : NestCtxOk ctx) {holes : List Expr}
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) :
    ∀ (T : List HomeEntry) (news : List (Name × List Level × List Expr × Nat ×
      List (ConstantVal × Nat))) {s₀ : CState}, CSOK mode env s₀ → (∀ e ∈ T, EntryScoped e) →
      (∀ q ∈ news, (∀ x ∈ q.2.2.1, WScoped (ctx.hiAt 0) x) ∧
        ∀ c ∈ q.2.2.2.2, c.1.type.hasFvar = false) →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ e ∈ v, EntryScoped e)
        (homeAdd (sharedOpsC mode (mkFEnv env)) env ctx holes T news)
        (homeAdd (fueledOpsM mode) env ctx holes T news)
  | T, [], _, hs, hT, _ => SimC.pure hs ⟨rfl, hT⟩
  | T, (I, us, a, nPc, ctors) :: rest, _, hs, hT, hnews => by
    unfold homeAdd
    have hq := hnews _ List.mem_cons_self
    have hrest := fun q hq' => hnews q (List.mem_cons_of_mem _ hq')
    split
    · exact homeAddS_sim hμ henv hc hholes hpar T rest hs hT hrest
    · refine SimC.bind (homeEntryNfsS_sim hμ henv hc hholes hpar I us hq.2 (key := some a)
        (fun ds h => by obtain rfl := Option.some.inj h; exact hq.1) hs)
        (fun s₁ nfs nfs' hs₁ hN => ?_)
      obtain ⟨rfl, hn⟩ := hN
      refine homeAddS_sim hμ henv hc hholes hpar _ rest hs₁ (fun e he => ?_) hrest
      rcases List.mem_append.mp he with he | he
      · exact hT e he
      · simp only [List.mem_singleton] at he; subst he; exact hn

theorem homeIterS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {ctx : NestCtx} (hc : NestCtxOk ctx) {holes : List Expr}
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) :
    ∀ (fuel : Nat) (T : List HomeEntry) {s₀ : CState}, CSOK mode env s₀ →
      (∀ e ∈ T, EntryScoped e) →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ e ∈ v, EntryScoped e)
        (homeIter (sharedOpsC mode (mkFEnv env)) env ctx holes fuel T)
        (homeIter (fueledOpsM mode) env ctx holes fuel T)
  | 0, T, _, hs, hT => SimC.pure hs ⟨rfl, hT⟩
  | fuel + 1, T, _, hs, hT => by
    unfold homeIter
    refine SimC.bind (homeAddS_sim hμ henv hc hholes hpar T _ hs hT (homeNews_ok hc hT))
      (fun s₁ T' T'' hs₁ hR => ?_)
    obtain ⟨rfl, hT'⟩ := hR
    split
    · exact SimC.pure hs₁ ⟨rfl, hT'⟩
    · exact homeIterS_sim hμ henv hc hholes hpar fuel T' hs₁ hT'

theorem homeTableAtS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {ctx : NestCtx} (hc : NestCtxOk ctx) {holes : List Expr}
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x)
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hcl : ∀ cs ∈ ctorsAs, ∀ c ∈ cs, c.1.type.hasFvar = false) (n : Nat) {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (homeTableAt (sharedOpsC mode (mkFEnv env)) env ctx holes ctorsAs n)
      (homeTableAt (fueledOpsM mode) env ctx holes ctorsAs n) := by
  unfold homeTableAt
  split
  · exact SimC.pure hs rfl
  · unfold homeTable
    refine SimC.mono (P := fun v w => v = w ∧ ∀ e ∈ v, EntryScoped e) (fun _ _ h => h.1) ?_
    refine SimC.bind (homeMembersS_sim hμ henv hc hholes hpar hcl hs)
      (fun s₁ T T' hs₁ hR => ?_)
    obtain ⟨rfl, hT⟩ := hR
    exact homeIterS_sim hμ henv hc hholes hpar _ T hs₁ hT

/-! ## The positivity stage -/

/-- **The install's positivity stage at the shared operations**: every
successful cached run is a fueled one. -/
theorem checkBlockPositivityS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    (p : BlockParts) (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type)
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkBlockPositivity (sharedOpsC mode (mkFEnv env)) env env.find? env.consts p cvTas
        ctorsAs)
      (checkBlockPositivity (fueledOpsM mode) env env.find? env.consts p cvTas ctorsAs) := by
  have hcl : ∀ cs ∈ ctorsAs, ∀ c ∈ cs, c.1.type.hasFvar = false :=
    fun cs hcs c hc => not_hasFvar_of_fvarsBelow_zero (hct cs hcs c hc).fvarsBelow
  unfold checkBlockPositivity
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ cvTa0 cvTa0' hs₁ hP => ?_)
  obtain ⟨rfl, h0⟩ := hP
  have hw0 : WScoped 0 cvTa0.type := hT _ (List.mem_of_mem_head? h0)
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ pq pq' hs₂ hP => ?_)
  obtain ⟨rfl, hpq⟩ := hP
  have hctx : NestCtxOk ⟨p.memberNames, p.lps, p.nP, p.nIdxs, pq.1, p.resSort, env.find?,
      env.consts⟩ :=
    ⟨fun ci hci => (henv ci hci).1,
      fun n ci hf => (henv ci (List.mem_of_find?_eq_some hf)).1⟩
  have hpar : ∀ x ∈ pq.1, WScoped (NestCtx.hiAt ⟨p.memberNames, p.lps, p.nP, p.nIdxs, pq.1,
      p.resSort, env.find?, env.consts⟩ 0) x := by
    intro x hx
    have := (openPisAtFvars_WScoped p.nP cvTa0.type 0 hpq hw0).1 x hx
    rw [Nat.zero_add] at this
    exact WScoped.mono (by simp [NestCtx.hiAt]) this
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ holes holes' hs₃ hP => ?_)
  obtain ⟨rfl, hh⟩ := hP
  refine SimC.bind (nestBlockCtorsS_sim hμ henv hctx (nestHoles_ok hctx hh) hpar ctorsAs {} hs₃
    hcl (fun _ _ hm => nomatch hm)) (fun s₄ r r' hs₄ hR => ?_)
  obtain ⟨rfl, -, hwN⟩ := hR
  rcases r with ⟨kinds, normals, st⟩
  dsimp only
  refine SimC.bind (checkAbsCtorTysAllS_sim hμ henv (nestHoles_ok hctx hh) hpar ctorsAs normals
    hs₄ hcl hwN) (fun s₅ u u' hs₅ _ => ?_)
  refine SimC.bind (homeTableAtS_sim hμ henv hctx (nestHoles_ok hctx hh) hpar
    (fun cs hcs c hc => hcl cs hcs c hc) _ hs₅) (fun s₆ homes homes' hs₆ hH => ?_)
  obtain rfl : homes = homes' := hH
  exact SimC.pure hs₆ rfl


end ConLeche.Cached
