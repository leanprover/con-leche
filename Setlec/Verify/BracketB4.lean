import Setlec.Verify.BridgeP
import Setlec.Verify.Promote

/-!
# The per-declaration snapshot bracket: seam theory and driver walks (task #64)

The default value pipeline runs each def/thm/opaque value under a
tier-two snapshot (`Setlec/Kernel/CheckerS.lean`: `openSnapshotM`,
`bracketValB4`, `closeSnapshotM`/`closeDiscardM`).  This module proves

* the *seam state theory* (battery item 3): opening preserves the
  tier-aware invariant (`ISOK.enable`), and the close — flush the
  index-carrying memos, truncate tier two, promote the stored output —
  re-establishes it at a flag-off state with the tier-one denotations
  intact (`ISOK.truncFlush`, `closeSnapshotM_eff`, `closeDiscardM_eff`);
* the *driver walks* (battery item 4): `checkDefnValPB4_sim`,
  `checkThmValPB4_sim`, `checkOpaqueValPB4_sim` and the dispatcher
  `checkDeclSP_sim` — the bracketed drivers simulate the same generic
  fueled `checkDecl` as the unbracketed ones, so the consistency chain
  (`Setlec/Model/ConsistencyP.lean`) covers the default binary.

The bracket seams are not store extensions (`Ext` carries the tier
flag and the tier-two prefix), so the walks compose the raw table
preservations (`KeepsO`) across the seams and reconstitute `Ext` at
the flag-off endpoints.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open EStore Expr

/-! ## Raw-table preservation across the seams -/

/-- The flag- and tier-two-free part of a store extension: the three
persistent tables only grow.  Every seam step preserves it, and at
flag-off endpoints (tier two empty on the left, flags equal) it
upgrades back to `Ext`. -/
structure KeepsO (st st' : EStore) : Prop where
  expr : ∀ (p : Nat) (n : ENode), st.nodes[p]? = some n → st'.nodes[p]? = some n
  lvl : ∀ (u : LIdx) (m : LNode), st.lnodes[u]? = some m → st'.lnodes[u]? = some m
  name : ∀ (i : NIdx) (m : NNode), st.nnodes[i]? = some m → st'.nnodes[i]? = some m

theorem KeepsO.refl (st : EStore) : KeepsO st st :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem KeepsO.trans {st₁ st₂ st₃ : EStore} (h₁ : KeepsO st₁ st₂)
    (h₂ : KeepsO st₂ st₃) : KeepsO st₁ st₃ :=
  ⟨fun p n h => h₂.expr p n (h₁.expr p n h),
   fun u m h => h₂.lvl u m (h₁.lvl u m h),
   fun i m h => h₂.name i m (h₁.name i m h)⟩

theorem EStore.Ext.keepsO {st st' : EStore} (h : Ext st st') :
    KeepsO st st' :=
  ⟨h.expr, h.lvl, h.name⟩

theorem KeepsO.enable (st : EStore) : KeepsO st st.enableTierTwo :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

/-- At a tier-two-empty left endpoint with equal flags, raw-table
preservation is a full extension. -/
theorem KeepsO.toExt {st st' : EStore} (h : KeepsO st st')
    (htn : st.tnodes.size = 0) (hf : st'.tierTwo = st.tierTwo) :
    Ext st st' :=
  ⟨h.expr, h.lvl, h.name,
   fun j n hj => absurd hj (by rw [getElem?_size_zero htn]; simp),
   hf⟩

/-! ## Seam state theory (battery item 3) -/

section Seam

variable {env : Env}

/-- Run form of a read-only store query. -/
theorem withStore_run {α : Type} (f : EStore → α) (s : IState) :
    Setlec.withStore f s = .ok (f s.store, s) := rfl

/-- Run form of `openSnapshotM` (the detach-swap collapses). -/
theorem openSnapshotM_run (s : IState) :
    openSnapshotM s = .ok ((), { s with store := s.store.enableTierTwo }) :=
  rfl

/-- Run form of `closeDiscardM`. -/
theorem closeDiscardM_run (s : IState) :
    closeDiscardM s = .ok
      ((), { s.flushed with store := s.store.truncateTierTwo }) := rfl

/-- Run form of `closeSnapshotM`. -/
theorem closeSnapshotM_run (jv : EIdx) (s : IState) :
    closeSnapshotM jv s = .ok
      ((s.store.truncateTierTwo.promoteE ⟨s.store.tnodes, #[], #[]⟩
          s.store.lnodes.size s.store.nnodes.size jv).1,
       { s.flushed with store :=
          (s.store.truncateTierTwo.promoteE ⟨s.store.tnodes, #[], #[]⟩
            s.store.lnodes.size s.store.nnodes.size jv).2 }) := rfl

/-- Opening the snapshot preserves the tier-aware invariant: the mode
switch is one flag write, invisible to every denotation. -/
theorem ISOK.enable {s : IState} (hs : ISOK env s) :
    ISOK env { s with store := s.store.enableTierTwo } := by
  have hT : ∀ i, s.store.enableTierTwo.denoteT i = s.store.denoteT i :=
    enableTierTwo_denoteT s.store
  have h1 : ∀ i, s.store.enableTierTwo.denote i = s.store.denote i :=
    enableTierTwo_denote s.store
  have hL : ∀ u, s.store.enableTierTwo.denoteL u = s.store.denoteL u :=
    fun u => denoteL_eq_of_lnodes_eq (st := s.store)
      (st' := s.store.enableTierTwo) rfl u
  have hN : ∀ q, s.store.enableTierTwo.denoteN q = s.store.denoteN q :=
    fun q => denoteN_eq_of_nnodes_eq (st := s.store)
      (st' := s.store.enableTierTwo) rfl q
  have hLL : ∀ us, denoteLList s.store.enableTierTwo.denoteL us
      = denoteLList s.store.denoteL us :=
    fun us => denoteLList_congr (fun u _ => hL u)
  refine ⟨enableTierTwo_twf hs.wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro n us i hl
    obtain ⟨nm, lus, ci, hnm, h0, hfind, h2⟩ := hs.constTy n us i hl
    exact ⟨nm, lus, ci, (hN n).trans hnm, (hLL us).trans h0, hfind,
      (hT i).trans h2⟩
  · intro n us i hl
    obtain ⟨nm, lus, cv, v, hh, hnm, h0, h1', h2⟩ := hs.constVal n us i hl
    exact ⟨nm, lus, cv, v, hh, (hN n).trans hnm, (hLL us).trans h0, h1',
      (hT i).trans h2⟩
  · intro c j us i hl
    obtain ⟨cn, jn, lus, cv, mI, rP, rules, rl, hcn, hjn, h0, h1', h2,
      h3⟩ := hs.ruleRhs c j us i hl
    exact ⟨cn, jn, lus, cv, mI, rP, rules, rl, (hN c).trans hcn,
      (hN j).trans hjn, (hLL us).trans h0, h1', h2, (hT i).trans h3⟩
  · intro i j hl
    obtain ⟨a, b, h1', h2, h3⟩ := hs.whnfCoreC i j hl
    exact ⟨a, b, (hT i).trans h1', (hT j).trans h2, h3⟩
  · intro i j hl
    obtain ⟨a, b, h1', h2, h3⟩ := hs.whnfC i j hl
    exact ⟨a, b, (hT i).trans h1', (hT j).trans h2, h3⟩
  · intro i j hl
    obtain ⟨a, b, h1', h2, h3⟩ := hs.inferC i j hl
    exact ⟨a, b, (hT i).trans h1', (hT j).trans h2, h3⟩
  · intro i j hl
    obtain ⟨a, b, h1', h2, h3⟩ := hs.annotC i j hl
    exact ⟨a, b, (hT i).trans h1', (hT j).trans h2, h3⟩
  · intro i j r hl
    obtain ⟨a, b, h1', h2, h3⟩ := hs.defeqC i j r hl
    exact ⟨a, b, (hT i).trans h1', (hT j).trans h2, h3⟩
  · intro u r hl
    obtain ⟨h1', h2⟩ := hs.lsimp u r hl
    exact ⟨h1', fun x hx => (hL r).trans (h2 x ((hL u).symm.trans hx))⟩
  · intro u b hl
    obtain ⟨h1', h2⟩ := hs.lnz u b hl
    exact ⟨h1', fun x hx => h2 x ((hL u).symm.trans hx)⟩
  · intro l r b hl
    obtain ⟨la, ra, h1', h2, h3⟩ := hs.eqv l r b hl
    exact ⟨la, ra, (hL l).trans h1', (hL r).trans h2, h3⟩
  · intro nm ent hl
    obtain ⟨hty, hval⟩ := hs.ienv nm ent hl
    exact ⟨(h1 ent.ty).trans hty,
      fun vE vi hv => (h1 vi).trans (hval vE vi hv)⟩

/-- The discarding close re-establishes the invariant at a flag-off
state: the flushed caches' clauses are vacuous, the level caches and
the interned environment survive (levels/names are single-tier and
truncation is invisible to the tier-one denotation). -/
theorem ISOK.truncFlush {s : IState} (hs : ISOK env s) :
    ISOK env { s.flushed with store := s.store.truncateTierTwo } := by
  have h1 : ∀ i, s.store.truncateTierTwo.denote i = s.store.denote i :=
    truncateTierTwo_denote s.store
  have hL : ∀ u, s.store.truncateTierTwo.denoteL u = s.store.denoteL u :=
    truncateTierTwo_denoteL s.store
  refine ⟨(truncateTierTwo_wf hs.wf).toTWF, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (intros; simp_all [IState.flushed]; done)
  · intro u r hl
    obtain ⟨h1', h2⟩ := hs.lsimp u r hl
    refine ⟨?_, fun x hx => (hL r).trans (h2 x ((hL u).symm.trans hx))⟩
    show u < s.store.truncateTierTwo.lnodes.size
    rw [truncateTierTwo_lnodes]
    exact h1'
  · intro u b hl
    obtain ⟨h1', h2⟩ := hs.lnz u b hl
    refine ⟨?_, fun x hx => h2 x ((hL u).symm.trans hx)⟩
    show u < s.store.truncateTierTwo.lnodes.size
    rw [truncateTierTwo_lnodes]
    exact h1'
  · intro l r b hl
    obtain ⟨la, ra, h1', h2, h3⟩ := hs.eqv l r b hl
    exact ⟨la, ra, (hL l).trans h1', (hL r).trans h2, h3⟩
  · intro nm ent hl
    obtain ⟨hty, hval⟩ := hs.ienv nm ent hl
    exact ⟨(h1 ent.ty).trans hty,
      fun vE vi hv => (h1 vi).trans (hval vE vi hv)⟩

/-- The discarding close, packaged: invariant re-established flag-off,
raw tables kept. -/
theorem closeDiscardM_eff {s : IState} (hs : ISOK env s) :
    ∀ (v : Unit) (s' : IState), closeDiscardM s = .ok (v, s') →
      ISOK env s' ∧ s'.store.tierTwo = false ∧
      KeepsO s.store s'.store ∧
      (∀ i x, s.store.denote i = some x → s'.store.denote i = some x) := by
  intro v s' hr
  rw [closeDiscardM_run] at hr
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  refine ⟨hs.truncFlush, rfl, ?_, ?_⟩
  · exact ⟨fun p n h => by rw [truncateTierTwo_nodes]; exact h,
      fun u m h => by rw [truncateTierTwo_lnodes]; exact h,
      fun i m h => by rw [truncateTierTwo_nnodes]; exact h⟩
  · intro i x hx
    rw [truncateTierTwo_denote]
    exact hx

/-- The promoting close, packaged: the stored output's tier-aware
denotation survives as a *tier-one* denotation of the promoted index;
the invariant is re-established flag-off and the raw tables kept. -/
theorem closeSnapshotM_eff {s : IState} (hs : ISOK env s) {jv : EIdx}
    {w : Expr} (hjv : s.store.denoteT jv = some w) :
    ∀ (r : EIdx) (s' : IState), closeSnapshotM jv s = .ok (r, s') →
      ISOK env s' ∧ s'.store.tierTwo = false ∧
      s'.store.denote r = some w ∧
      KeepsO s.store s'.store ∧
      (∀ i x, s.store.denote i = some x → s'.store.denote i = some x) := by
  intro r s' hr
  rw [closeSnapshotM_run] at hr
  injection hr with h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h1
  obtain ⟨hwfP, hextP, hdenP⟩ := promoteE_spec (stP := s.store)
    (st0 := s.store.truncateTierTwo) hs.wf (truncateTierTwo_wf hs.wf)
    (fun i x hx => by rw [truncateTierTwo_denote]; exact hx)
    (fun u l hl => by rw [truncateTierTwo_denoteL]; exact hl)
    (fun q nm hn => by rw [truncateTierTwo_denoteN]; exact hn)
    (hl := #[]) (hn := #[]) hjv
  have hisok' : ISOK env
      { s.flushed with store :=
        (s.store.truncateTierTwo.promoteE ⟨s.store.tnodes, #[], #[]⟩
          s.store.lnodes.size s.store.nnodes.size jv).2 } := by
    have := (hs.truncFlush (env := env)).withStore hwfP.toTWF hextP
    simpa using this
  refine ⟨hisok', ?_, hdenP, ?_, ?_⟩
  · show (s.store.truncateTierTwo.promoteE _ _ _ jv).2.tierTwo = false
    rw [hextP.flag]
    rfl
  · refine ⟨fun p n h => ?_, fun u m h => ?_, fun i m h => ?_⟩
    · exact hextP.expr p n (by rw [truncateTierTwo_nodes]; exact h)
    · exact hextP.lvl u m (by rw [truncateTierTwo_lnodes]; exact h)
    · exact hextP.name i m (by rw [truncateTierTwo_nnodes]; exact h)
  · intro i x hx
    refine denote_mono hextP ?_
    rw [truncateTierTwo_denote]
    exact hx

end Seam

/-! ## Run dissection (local twins of the Model-layer toolkit; the
Model files import this module's consumers, so the helpers live here
under distinct names) -/

/-- Dissect a successful `CheckIM` bind. -/
theorem bindB4_ok {α β : Type} {x : CheckIM α} {k : α → CheckIM β}
    {s₀ : IState} {v : β} {s' : IState}
    (h : (x >>= k) s₀ = .ok (v, s')) :
    ∃ a s₁, x s₀ = .ok (a, s₁) ∧ k a s₁ = .ok (v, s') := by
  simp only [Bind.bind, StateT.bind] at h
  cases hx : x s₀ with
  | error e => rw [hx] at h; exact nomatch h
  | ok pr =>
    obtain ⟨a, s₁⟩ := pr
    rw [hx] at h
    exact ⟨a, s₁, rfl, h⟩

theorem pureB4_ok {α : Type} {a : α} {s₀ : IState} {v : α} {s' : IState}
    (h : (pure a : CheckIM α) s₀ = .ok (v, s')) : a = v ∧ s₀ = s' := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at h
  exact h

/-- A reduced-form throw composed with anything never succeeds. -/
theorem throwB4_bind_ok {α β : Type} {e : CheckError} {k : α → CheckIM β}
    {s : IState} {v : β} {s' : IState}
    (h : StateT.bind (throw e) k s = .ok (v, s')) : False :=
  nomatch h

/-! ## The bracketed middle (battery item 4) -/

section Walks

variable {env : Env} {s₀ : IState}

/-- The bracketed middle of the def/thm value pipeline, as a run
effect: from a flag-off invariant state, a successful `bracketValB4`
re-establishes the invariant flag-off, *extends* the store (the
snapshot's tier-two content died at the close; the promoted output and
the bracket's level/name interns persist), returns the readback `vE`
with the promoted index denoting it tier-one, and its components are
backed by fueled runs of the generic annotate/infer/defeq at one joined
fuel — the ingredients of the spec-side `checkDefnVal`/`checkThmVal`
run the driver walks assemble. -/
theorem bracketValB4_eff (henv : EnvWF env) {cvA : ConstantVal}
    {jty value : EIdx} {ve : Expr}
    (htf : WScoped 0 cvA.type)
    (hjty : s₀.store.denote jty = some cvA.type)
    (hdenv : s₀.store.denote value = some ve) (hwv : WScoped 0 ve)
    (hs : ISOK env s₀) (hoff : s₀.store.tierTwo = false) :
    IEff env s₀ (fun s r =>
      s.store.tierTwo = false ∧
      s.store.denote r.2.1 = some r.1 ∧ WScoped 0 r.1 ∧
      ∃ F, (fueledOpsM.annotate env 0 ve).val F = .ok r.1 ∧
        r.1.allLevelParamsDefined cvA.levelParams = true ∧
        r.1.constsResolve env = true ∧
        ∃ wt, (fueledOpsM.inferType env 0 r.1).val F = .ok wt ∧
          (fueledOpsM.isDefEq env 0 wt cvA.type).val F = .ok r.2.2)
      (bracketValB4 (mkFEnv env) cvA jty value) := by
  intro r s' hrun
  unfold bracketValB4 at hrun
  -- open the snapshot
  obtain ⟨u₀, s₂, hop, hrun⟩ := bindB4_ok hrun
  rw [openSnapshotM_run] at hop
  injection hop with hop
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hop
  have hs₂ : ISOK env { s₀ with store := s₀.store.enableTierTwo } :=
    hs.enable
  have hdenvT₂ : s₀.store.enableTierTwo.denoteT value = some ve := by
    rw [enableTierTwo_denoteT]
    exact EStore.denoteT_of_denote hs.wf hdenv
  have hjty₂ : s₀.store.enableTierTwo.denote jty = some cvA.type := by
    rw [enableTierTwo_denote]
    exact hjty
  -- annotate under the snapshot
  obtain ⟨jv, s₃, hann, hrun⟩ := bindB4_ok hrun
  obtain ⟨hs₃, hext₂₃, w, ⟨hjv, hww⟩, F₁, hFann⟩ :=
    ((ssimI env henv checkFuel).annotate hs₂ hdenvT₂ hwv) jv s₃ hann
  -- post-annotate guards (join-point compiled: reduce the state
  -- layer, rewrite the memoized walkers to their `Expr` counterparts,
  -- split)
  simp only [Setlec.withStore, Functor.map, StateT.map, get, getThe,
    MonadStateOf.get, StateT.get, Except.map, Bind.bind, StateT.bind,
    Except.bind, pure, StateT.pure, Except.pure] at hrun
  rw [show s₃.store.allLevelParamsDefinedI cvA.levelParams jv
        = w.allLevelParamsDefined cvA.levelParams from
      allLevelParamsDefinedI_spec hs₃.wf hjv] at hrun
  by_cases h₁ : w.allLevelParamsDefined cvA.levelParams = true
  case neg =>
    rw [if_neg h₁] at hrun
    exact absurd hrun throwB4_bind_ok
  rw [if_pos h₁] at hrun
  simp only [StateT.map, StateT.get, StateT.bind, Bind.bind,
    Except.map, Except.bind, pure, StateT.pure, Except.pure] at hrun
  rw [show constsResolveFI s₃.store (mkFEnv env) jv
        = w.constsResolve env from
      constsResolveFI_spec hs₃.wf hjv] at hrun
  by_cases h₂ : w.constsResolve env = true
  case neg =>
    rw [if_neg h₂] at hrun
    exact absurd hrun throwB4_bind_ok
  rw [if_pos h₂] at hrun
  -- readback
  obtain ⟨vE, s₃e, hrb, hrun⟩ := bindB4_ok hrun
  obtain ⟨hs₃e, hext₃e, rfl⟩ := (readbackEM_eff hs₃ hjv) vE s₃e hrb
  have hjv₃e : s₃e.store.denoteT jv = some vE := denoteT_mono hext₃e hjv
  -- infer
  obtain ⟨jvt, s₄, hinf, hrun⟩ := bindB4_ok hrun
  obtain ⟨hs₄, hext₄, wt, ⟨hjvt, hwt⟩, F₂, hFinf⟩ :=
    ((ssimI env henv checkFuel).infer hs₃e hjv₃e hww) jvt s₄ hinf
  -- defeq against the stated type
  have hjty₄ : s₄.store.denote jty = some cvA.type :=
    denote_mono hext₄ (denote_mono hext₃e (denote_mono hext₂₃ hjty₂))
  obtain ⟨ok, s₅, hdeq, hrun⟩ := bindB4_ok hrun
  obtain ⟨hs₅, hext₅, ok', hok, F₃, hFdeq⟩ :=
    ((ssimI env henv checkFuel).defeq hs₄ hjvt
      (EStore.denoteT_of_denote hs₄.wf hjty₄) hwt htf) ok s₅ hdeq
  obtain rfl : ok = ok' := hok
  -- close the snapshot
  obtain ⟨jv', s₆, hcl, hrun⟩ := bindB4_ok hrun
  have hjv₅ : s₅.store.denoteT jv = some vE :=
    denoteT_mono hext₅ (denoteT_mono hext₄ hjv₃e)
  obtain ⟨hs₆, hoff₆, hjv', hkeep₆, hden₆⟩ :=
    closeSnapshotM_eff hs₅ hjv₅ jv' s₆ hcl
  obtain ⟨rfl, rfl⟩ := pureB4_ok hrun
  -- assemble
  have hkeep : KeepsO s₀.store s₆.store :=
    ((((KeepsO.enable s₀.store).trans hext₂₃.keepsO).trans
      hext₃e.keepsO).trans (hext₄.keepsO.trans hext₅.keepsO)).trans
      hkeep₆
  have hext : Ext s₀.store s₆.store :=
    hkeep.toExt (hs.wf.toff_tnil hoff) (by rw [hoff₆, hoff])
  refine ⟨hs₆, hext, hoff₆, hjv', hww, max F₁ (max F₂ F₃), ?_, h₁, h₂,
    wt, ?_, ?_⟩
  · exact (fueledOpsM.annotate env 0 ve).property
      (Nat.le_max_left _ _) hFann
  · exact (fueledOpsM.inferType env 0 vE).property
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right F₁ _)) hFinf
  · exact (fueledOpsM.isDefEq env 0 wt cvA.type).property
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right F₁ _)) hFdeq


/-- `checkDefnValPB4` simulates the generic `checkDefnVal`: the
snapshot bracket is invisible to the fueled spec. -/
theorem checkDefnValPB4_sim (henv : EnvWF env) {cvA : ConstantVal}
    {jty : EIdx} {value : EIdx} {ve : Expr} {hint : ReducibilityHint}
    (htf : WScoped 0 cvA.type) (hjty : s₀.store.denote jty = some cvA.type)
    (hdenv : s₀.store.denote value = some ve) (hs : ISOK env s₀)
    (hoff : s₀.store.tierTwo = false) :
    SimAt env s₀ (fun _ v w => v.env = w ∧ v = mkFEnv v.env ∧
        ∀ cv' v' h', v.env.find? cvA.name = some (.defnInfo cv' v' h') →
          v'.hasFvar = false)
      (checkDefnValPB4 (mkFEnv env) cvA jty value hint)
      (checkDefnVal fueledOpsM env cvA ve hint) := by
  intro v' s' hrun
  have hdenvT : s₀.store.denoteT value = some ve :=
    EStore.denoteT_of_denote hs.wf hdenv
  unfold checkDefnValPB4 at hrun
  simp only [Setlec.withStore, Functor.map, StateT.map, get, getThe,
    MonadStateOf.get, StateT.get, Bind.bind, StateT.bind, Except.bind,
    pure, StateT.pure, Except.pure] at hrun
  rw [show s₀.store.looseBVarsBoundedI 0 value
        = ve.looseBVarsBounded 0 from
      looseBVarsBoundedI_spec hs.wf hdenvT] at hrun
  by_cases h1 : ve.looseBVarsBounded 0 = true
  case neg =>
    rw [if_neg h1] at hrun
    exact absurd hrun throwB4_bind_ok
  rw [if_pos h1] at hrun
  simp only [StateT.map, StateT.get, StateT.bind, Bind.bind,
    Except.bind, pure, StateT.pure, Except.pure] at hrun
  rw [show s₀.store.hasFvarI value = ve.hasFvar from
      hasFvarI_spec hs.wf hdenvT] at hrun
  by_cases h2 : ve.hasFvar = true
  case pos =>
    rw [if_pos h2] at hrun
    exact absurd hrun throwB4_bind_ok
  rw [if_neg h2] at hrun
  have hwv : WScoped 0 ve :=
    WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)
  -- the bracketed middle
  obtain ⟨r, s₁, hbr, hrun⟩ := bindB4_ok hrun
  obtain ⟨hs₁, hext₁, hoff₁, hdenr, hwvE, F, hFann, hpar, hcon, wt,
    hFinf, hFdeq⟩ :=
    (bracketValB4_eff henv htf hjty hdenv hwv hs hoff) r s₁ hbr
  obtain ⟨vE, jv', ok⟩ := r
  -- the postponed verdict
  cases ok with
  | false =>
    rw [if_neg (by simp)] at hrun
    exact absurd hrun throwB4_bind_ok
  | true =>
  rw [if_pos rfl] at hrun
  -- record and push
  obtain ⟨u, s₂, hrec, hrun⟩ := bindB4_ok hrun
  rw [recordIConst_run] at hrec
  injection hrec with hrec
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hrec
  obtain ⟨hv', rfl⟩ := pureB4_ok hrun
  subst hv'
  have hs₂ : ISOK env
      { s₁ with ienv := s₁.ienv.insert cvA.name ⟨cvA.type, jty,
        some (vE, jv')⟩ } :=
    hs₁.insertIEnv (denote_mono hext₁ hjty)
      (fun vE' vi h => by cases h; exact hdenr)
  refine ⟨hs₂, hext₁, ⟨.defnInfo cvA vE hint :: env.consts⟩,
    ⟨rfl, mkFEnv_push env _, ?_⟩, F, ?_⟩
  · intro cv' v'' h' hf
    rw [show ((mkFEnv env).push (.defnInfo cvA vE hint)).env =
      ⟨.defnInfo cvA vE hint :: env.consts⟩ from rfl] at hf
    rw [Env.find?_cons, if_pos (show (ConstantInfo.defnInfo cvA vE
      hint).name = cvA.name from rfl)] at hf
    simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf
    obtain ⟨-, rfl, -⟩ := hf
    exact not_hasFvar_of_fvarsBelow_zero hwvE.fvarsBelow
  · -- assemble the fueled spec run
    unfold checkDefnVal
    simp only [FueledM.atF_bind, FueledM.atF_ite, if_pos h1, if_neg h2]
    rw [hFann]
    simp only [Bind.bind, Except.bind, if_pos hpar, if_pos hcon]
    rw [hFinf]
    simp only [Bind.bind, Except.bind]
    rw [hFdeq]
    simp only [Bind.bind, Except.bind, if_pos rfl]
    rfl

/-- `checkThmValPB4` simulates the generic `checkThmVal`. -/
theorem checkThmValPB4_sim (henv : EnvWF env) {cvA : ConstantVal}
    {jty : EIdx} {value : EIdx} {ve : Expr}
    (htf : WScoped 0 cvA.type) (hjty : s₀.store.denote jty = some cvA.type)
    (hdenv : s₀.store.denote value = some ve) (hs : ISOK env s₀)
    (hoff : s₀.store.tierTwo = false) :
    SimAt env s₀ (fun _ v w => v.env = w ∧ v = mkFEnv v.env)
      (checkThmValPB4 (mkFEnv env) cvA jty value)
      (checkThmVal fueledOpsM env cvA ve) := by
  intro v' s' hrun
  unfold checkThmValPB4 at hrun
  -- the is-a-proposition prefix
  obtain ⟨jsty, sA, hinfT, hrun⟩ := bindB4_ok hrun
  obtain ⟨hsA, hextA, wsty, ⟨hjsty, hwsty⟩, F₀, hFinfT⟩ :=
    ((ssimI env henv checkFuel).infer hs
      (EStore.denoteT_of_denote hs.wf hjty) htf) jsty sA hinfT
  obtain ⟨ul, sB, hsx, hrun⟩ := bindB4_ok hrun
  obtain ⟨hsB, hextB, ul', hul, F₀', hFsx⟩ :=
    (opSIx_sim henv hsA hjsty hwsty) ul sB hsx
  obtain rfl : ul = ul' := hul
  obtain ⟨beq, sC, hlf, hrun⟩ := bindB4_ok hrun
  cases hiso : Level.isEquiv ul .zero with
  | none =>
    rw [show (liftFueled "level comparison" (Level.isEquiv ul .zero) :
        CheckIM Bool) = throw (.internal
          s!"fuel exhausted: level comparison") from by
      rw [hiso]; rfl] at hlf
    exact nomatch hlf
  | some b =>
    rw [show (liftFueled "level comparison" (Level.isEquiv ul .zero) :
        CheckIM Bool) = pure b from by rw [hiso]; rfl] at hlf
    obtain ⟨rfl, rfl⟩ := pureB4_ok hlf
    cases b with
    | false =>
      rw [if_neg (by simp)] at hrun
      exact absurd hrun throwB4_bind_ok
    | true =>
    rw [if_pos rfl] at hrun
    have hoffC : sB.store.tierTwo = false :=
      tierOffExt hextB (tierOffExt hextA hoff)
    have hjtyC : sB.store.denote jty = some cvA.type :=
      denote_mono hextB (denote_mono hextA hjty)
    have hdenvC : sB.store.denote value = some ve :=
      denote_mono hextB (denote_mono hextA hdenv)
    have hdenvTC : sB.store.denoteT value = some ve :=
      EStore.denoteT_of_denote hsB.wf hdenvC
    -- the value guards
    simp only [Setlec.withStore, Functor.map, StateT.map, get, getThe,
      MonadStateOf.get, StateT.get, Bind.bind, StateT.bind, Except.bind,
      pure, StateT.pure, Except.pure] at hrun
    rw [show sB.store.looseBVarsBoundedI 0 value
          = ve.looseBVarsBounded 0 from
        looseBVarsBoundedI_spec hsB.wf hdenvTC] at hrun
    by_cases h1 : ve.looseBVarsBounded 0 = true
    case neg =>
      rw [if_neg h1] at hrun
      exact absurd hrun throwB4_bind_ok
    rw [if_pos h1] at hrun
    simp only [StateT.map, StateT.get, StateT.bind, Bind.bind,
      Except.bind, pure, StateT.pure, Except.pure] at hrun
    rw [show sB.store.hasFvarI value = ve.hasFvar from
        hasFvarI_spec hsB.wf hdenvTC] at hrun
    by_cases h2 : ve.hasFvar = true
    case pos =>
      rw [if_pos h2] at hrun
      exact absurd hrun throwB4_bind_ok
    rw [if_neg h2] at hrun
    have hwv : WScoped 0 ve :=
      WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)
    -- the bracketed middle
    obtain ⟨r, s₁, hbr, hrun⟩ := bindB4_ok hrun
    obtain ⟨hs₁, hext₁, hoff₁, hdenr, hwvE, F, hFann, hpar, hcon, wt,
      hFinf, hFdeq⟩ :=
      (bracketValB4_eff henv htf hjtyC hdenvC hwv hsB hoffC) r s₁ hbr
    obtain ⟨vE, jv', ok⟩ := r
    cases ok with
    | false =>
      rw [if_neg (by simp)] at hrun
      exact absurd hrun throwB4_bind_ok
    | true =>
    rw [if_pos rfl] at hrun
    obtain ⟨u, s₂, hrec, hrun⟩ := bindB4_ok hrun
    rw [recordIConst_run] at hrec
    injection hrec with hrec
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hrec
    obtain ⟨hv', rfl⟩ := pureB4_ok hrun
    subst hv'
    have hs₂ : ISOK env
        { s₁ with ienv := s₁.ienv.insert cvA.name ⟨cvA.type, jty,
          some (vE, jv')⟩ } :=
      hs₁.insertIEnv (denote_mono hext₁ hjtyC)
        (fun vE' vi h => by cases h; exact hdenr)
    refine ⟨hs₂, hextA.trans (hextB.trans hext₁),
      ⟨.thmInfo cvA vE :: env.consts⟩,
      ⟨rfl, mkFEnv_push env _⟩, max F₀ (max F₀' F), ?_⟩
    -- assemble the fueled spec run
    unfold checkThmVal
    simp only [FueledM.atF_bind, FueledM.atF_ite, liftFueled_atF]
    rw [(fueledOpsM.inferType env 0 cvA.type).property
      (Nat.le_max_left _ _) hFinfT]
    simp only [Bind.bind, Except.bind]
    rw [(fueledOpsM.ensureSort env 0 wsty).property
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right F₀ _)) hFsx]
    simp only [Bind.bind, Except.bind]
    rw [hiso]
    simp only [liftFueled, Bind.bind, Except.bind, pure, Except.pure,
      if_pos rfl, if_pos h1, if_neg h2]
    rw [(fueledOpsM.annotate env 0 ve).property
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right F₀ _)) hFann]
    simp only [Bind.bind, Except.bind, if_pos hpar, if_pos hcon]
    rw [(fueledOpsM.inferType env 0 vE).property
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right F₀ _)) hFinf]
    simp only [Bind.bind, Except.bind]
    rw [(fueledOpsM.isDefEq env 0 wt cvA.type).property
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right F₀ _)) hFdeq]
    simp only [Bind.bind, Except.bind, if_pos rfl]
    rfl

/-- `checkOpaqueValPB4` simulates the generic `checkOpaqueVal` (the
snapshot is fully discarded: opaques store nothing). -/
theorem checkOpaqueValPB4_sim (henv : EnvWF env) {cvA : ConstantVal}
    {jty : EIdx} {value : EIdx} {ve : Expr}
    (htf : WScoped 0 cvA.type) (hjty : s₀.store.denote jty = some cvA.type)
    (hdenv : s₀.store.denote value = some ve) (hs : ISOK env s₀)
    (hoff : s₀.store.tierTwo = false) :
    SimAt env s₀ (fun _ v w => (v.env = w ∧ v = mkFEnv v.env) ∧
        ve.hasFvar = false)
      (checkOpaqueValPB4 (mkFEnv env) cvA jty value)
      (checkOpaqueVal fueledOpsM env cvA ve) := by
  intro v' s' hrun
  have hdenvT : s₀.store.denoteT value = some ve :=
    EStore.denoteT_of_denote hs.wf hdenv
  unfold checkOpaqueValPB4 at hrun
  simp only [Setlec.withStore, Functor.map, StateT.map, get, getThe,
    MonadStateOf.get, StateT.get, Bind.bind, StateT.bind, Except.bind,
    pure, StateT.pure, Except.pure] at hrun
  rw [show s₀.store.looseBVarsBoundedI 0 value
        = ve.looseBVarsBounded 0 from
      looseBVarsBoundedI_spec hs.wf hdenvT] at hrun
  by_cases h1 : ve.looseBVarsBounded 0 = true
  case neg =>
    rw [if_neg h1] at hrun
    exact absurd hrun throwB4_bind_ok
  rw [if_pos h1] at hrun
  simp only [StateT.map, StateT.get, StateT.bind, Bind.bind,
    Except.bind, pure, StateT.pure, Except.pure] at hrun
  rw [show s₀.store.hasFvarI value = ve.hasFvar from
      hasFvarI_spec hs.wf hdenvT] at hrun
  by_cases h2 : ve.hasFvar = true
  case pos =>
    rw [if_pos h2] at hrun
    exact absurd hrun throwB4_bind_ok
  rw [if_neg h2] at hrun
  have hwv : WScoped 0 ve :=
    WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)
  -- open the snapshot
  obtain ⟨u₀, sE, hop, hrun⟩ := bindB4_ok hrun
  rw [openSnapshotM_run] at hop
  injection hop with hop
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hop
  have hs₂ : ISOK env { s₀ with store := s₀.store.enableTierTwo } :=
    hs.enable
  have hdenvT₂ : s₀.store.enableTierTwo.denoteT value = some ve := by
    rw [enableTierTwo_denoteT]
    exact hdenvT
  -- annotate under the snapshot
  obtain ⟨jv, s₃, hann, hrun⟩ := bindB4_ok hrun
  obtain ⟨hs₃, hext₂₃, w, ⟨hjv, hww⟩, F₁, hFann⟩ :=
    ((ssimI env henv checkFuel).annotate hs₂ hdenvT₂ hwv) jv s₃ hann
  -- post-annotate guards
  simp only [Setlec.withStore, Functor.map, StateT.map, get, getThe,
    MonadStateOf.get, StateT.get, Bind.bind, StateT.bind, Except.bind,
    pure, StateT.pure, Except.pure] at hrun
  rw [show s₃.store.allLevelParamsDefinedI cvA.levelParams jv
        = w.allLevelParamsDefined cvA.levelParams from
      allLevelParamsDefinedI_spec hs₃.wf hjv] at hrun
  by_cases hp₁ : w.allLevelParamsDefined cvA.levelParams = true
  case neg =>
    rw [if_neg hp₁] at hrun
    exact absurd hrun throwB4_bind_ok
  rw [if_pos hp₁] at hrun
  simp only [StateT.map, StateT.get, StateT.bind, Bind.bind,
    Except.bind, pure, StateT.pure, Except.pure] at hrun
  rw [show constsResolveFI s₃.store (mkFEnv env) jv
        = w.constsResolve env from
      constsResolveFI_spec hs₃.wf hjv] at hrun
  by_cases hp₂ : w.constsResolve env = true
  case neg =>
    rw [if_neg hp₂] at hrun
    exact absurd hrun throwB4_bind_ok
  rw [if_pos hp₂] at hrun
  -- infer, defeq
  obtain ⟨jvt, s₄, hinf, hrun⟩ := bindB4_ok hrun
  obtain ⟨hs₄, hext₄, wt, ⟨hjvt, hwt⟩, F₂, hFinf⟩ :=
    ((ssimI env henv checkFuel).infer hs₃ hjv hww) jvt s₄ hinf
  have hjty₄ : s₄.store.denote jty = some cvA.type := by
    refine denote_mono hext₄ (denote_mono hext₂₃ ?_)
    rw [enableTierTwo_denote]
    exact hjty
  obtain ⟨ok, s₅, hdeq, hrun⟩ := bindB4_ok hrun
  obtain ⟨hs₅, hext₅, ok', hok, F₃, hFdeq⟩ :=
    ((ssimI env henv checkFuel).defeq hs₄ hjvt
      (EStore.denoteT_of_denote hs₄.wf hjty₄) hwt htf) ok s₅ hdeq
  obtain rfl : ok = ok' := hok
  -- discard the snapshot
  obtain ⟨u₁, s₆, hcl, hrun⟩ := bindB4_ok hrun
  obtain ⟨hs₆, hoff₆, hkeep₆, hden₆⟩ := closeDiscardM_eff hs₅ u₁ s₆ hcl
  cases ok with
  | false =>
    rw [if_neg (by simp)] at hrun
    exact absurd hrun throwB4_bind_ok
  | true =>
  rw [if_pos rfl] at hrun
  obtain ⟨u, s₇, hrec, hrun⟩ := bindB4_ok hrun
  rw [recordIConst_run] at hrec
  injection hrec with hrec
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hrec
  obtain ⟨hv', rfl⟩ := pureB4_ok hrun
  subst hv'
  have hkeep : KeepsO s₀.store s₆.store :=
    ((((KeepsO.enable s₀.store).trans hext₂₃.keepsO).trans
      hext₄.keepsO).trans hext₅.keepsO).trans hkeep₆
  have hext : Ext s₀.store s₆.store :=
    hkeep.toExt (hs.wf.toff_tnil hoff) (by rw [hoff₆, hoff])
  have hs₇ : ISOK env
      { s₆ with ienv := s₆.ienv.insert cvA.name ⟨cvA.type, jty,
        none⟩ } :=
    hs₆.insertIEnv (denote_mono hext hjty)
      (fun vE' vi h => nomatch h)
  refine ⟨hs₇, hext, ⟨.axiomInfo cvA :: env.consts⟩,
    ⟨⟨rfl, mkFEnv_push env _⟩, Bool.not_eq_true _ ▸ h2⟩,
    max F₁ (max F₂ F₃), ?_⟩
  unfold checkOpaqueVal
  simp only [FueledM.atF_bind, FueledM.atF_ite, if_pos h1, if_neg h2]
  rw [(fueledOpsM.annotate env 0 ve).property (Nat.le_max_left _ _) hFann]
  simp only [Bind.bind, Except.bind, if_pos hp₁, if_pos hp₂]
  rw [(fueledOpsM.inferType env 0 w).property
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right F₁ _)) hFinf]
  simp only [Bind.bind, Except.bind]
  rw [(fueledOpsM.isDefEq env 0 wt cvA.type).property
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right F₁ _)) hFdeq]
  simp only [Bind.bind, Except.bind, if_pos rfl]
  rfl

/-- Forget a simulation's fueled counterpart: any simulated step is in
particular a state-respecting effect. -/
theorem IEff.of_sim {β α : Type} {P : IState → β → α → Prop}
    {c : CheckIM β} {p : FueledM α} (h : SimAt env s₀ P c p) :
    IEff env s₀ (fun _ _ => True) c := by
  intro v' s' hr
  obtain ⟨hs', hext, -⟩ := h v' s' hr
  exact ⟨hs', hext, trivial⟩

/-- The non-inductive branches of THE default dispatcher `checkDeclSP`
simulate the generic `checkDecl` at the fueled families on the denoted
declaration: the def/thm/opaque value pipeline through the snapshot
bracket, the pinned-cert branches and the install-only kinds through
the unbracketed path (whose `checkConstantValP` prefix re-run is a
state-respecting effect — memoized passes, same canonical indices). -/
theorem checkDeclSP_sim (henv : EnvWF env) (hs : ISOK env s₀)
    (hoff : s₀.store.tierTwo = false)
    {pd : DeclP} {d : Declaration}
    (hden : denoteDeclP s₀.store pd = some d)
    (hnotind : ∀ block, pd ≠ .indDecl block) :
    SimAt env s₀ (fun _ v w => v.env = w ∧ v = mkFEnv v.env)
      (checkDeclSP (mkFEnv env) pd)
      (checkDecl fueledOpsM env d) := by
  cases pd with
  | indDecl block => exact absurd rfl (hnotind block)
  | basisDecl kind =>
    exact checkDeclSPPlain_sim henv hs hoff hden hnotind
  | axiomDecl cvp =>
    exact checkDeclSPPlain_sim henv hs hoff hden hnotind
  | thmDecl cvp value =>
    simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hden
    obtain ⟨cv0, ⟨tyE, htyE, rfl⟩, ve, hve, rfl⟩ := hden
    unfold checkDeclSP checkDecl
    dsimp only
    refine SimAt.bind (checkConstantValP_sim henv hs hoff htyE)
      (fun s₁ pr cvA hs₁ hext₁ hP => ?_)
    obtain ⟨cvR, jty⟩ := pr
    obtain ⟨rfl, hname, hwty, hjty⟩ := hP
    dsimp only at hjty ⊢
    exact SimAt.mono (fun s v w h => h) (checkThmValPB4_sim henv hwty
      hjty (denote_mono hext₁ hve) hs₁ (tierOffExt hext₁ hoff))
  | opaqueDecl cvp value =>
    have hdenP := hden
    simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hden
    obtain ⟨cv0, ⟨tyE, htyE, rfl⟩, ve, hve, rfl⟩ := hden
    show SimAt env s₀ _ (checkDeclSP (mkFEnv env)
      (.opaqueDecl cvp value)) _
    unfold checkDeclSP
    dsimp only
    by_cases hred : reduceOpNames.contains cvp.name = true
    · rw [if_pos hred]
      exact checkDeclSPPlain_sim henv hs hoff hdenP hnotind
    rw [if_neg hred]
    unfold checkDecl
    dsimp only
    refine SimAt.bind (checkConstantValP_sim henv hs hoff htyE)
      (fun s₁ pr cvA hs₁ hext₁ hP => ?_)
    obtain ⟨cvR, jty⟩ := pr
    obtain ⟨rfl, hname, hwty, hjty⟩ := hP
    dsimp only at hjty hname ⊢
    have hoff₁ : s₁.store.tierTwo = false := tierOffExt hext₁ hoff
    rw [← bind_pure (checkOpaqueValPB4 (mkFEnv env) cvR jty value)]
    refine SimAt.bind (checkOpaqueValPB4_sim henv hwty hjty
        (denote_mono hext₁ hve) hs₁ hoff₁)
      (fun s₂ fe2 env2 hs₂ hext₂ hP₂ => ?_)
    obtain ⟨⟨henvEq, hmk⟩, -⟩ := hP₂
    subst henvEq
    rw [hmk]
    simp only [mkFEnv_env]
    rw [show reduceOpNames.contains cvR.name = false from by
      rw [hname]; exact Bool.not_eq_true _ ▸ hred]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.pure hs₂ ⟨rfl, hmk ▸ hmk⟩
  | defnDecl cvp value hint =>
    have hdenP := hden
    simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hden
    obtain ⟨cv0, ⟨tyE, htyE, rfl⟩, ve, hve, rfl⟩ := hden
    show SimAt env s₀ _ (checkDeclSP (mkFEnv env)
      (.defnDecl cvp value hint)) _
    unfold checkDeclSP
    dsimp only
    by_cases hb : (natOpNames.contains cvp.name ||
        natDivModNames.contains cvp.name) = true
    · rw [if_pos hb]
      exact checkDeclSPPlain_sim henv hs hoff hdenP hnotind
    rw [if_neg hb]
    obtain ⟨h1, h4⟩ : ¬(natOpNames.contains cvp.name = true) ∧
        ¬(natDivModNames.contains cvp.name = true) := by
      simpa [not_or] using hb
    unfold checkDecl
    dsimp only
    refine SimAt.bind (checkConstantValP_sim henv hs hoff htyE)
      (fun s₁ pr cvA hs₁ hext₁ hP => ?_)
    obtain ⟨cvR, jty⟩ := pr
    obtain ⟨rfl, hname, hwty, hjty⟩ := hP
    dsimp only at hjty hname ⊢
    rw [← bind_pure (checkDefnValPB4 (mkFEnv env) cvR jty value hint)]
    refine SimAt.bind (checkDefnValPB4_sim henv hwty hjty
        (denote_mono hext₁ hve) hs₁ (tierOffExt hext₁ hoff))
      (fun s₂ fe2 env2 hs₂ hext₂ hP₂ => ?_)
    obtain ⟨henvEq, hmk, -⟩ := hP₂
    subst henvEq
    rw [hmk]
    simp only [mkFEnv_env]
    rw [show natOpNames.contains cvR.name = false from by
        rw [hname]; exact Bool.not_eq_true _ ▸ h1,
      show natDivModNames.contains cvR.name = false from by
        rw [hname]; exact Bool.not_eq_true _ ▸ h4]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.pure hs₂ ⟨rfl, hmk ▸ hmk⟩

end Walks

end Setlec
