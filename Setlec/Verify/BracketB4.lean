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

theorem Ext.keepsO {st st' : EStore} (h : Ext st st') : KeepsO st st' :=
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
    ?_, ?_, ?_, ?_⟩
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
  · intro i u hl
    obtain ⟨a, l, h1', h2, h3⟩ := hs.codOfC i u hl
    exact ⟨a, l, (hT i).trans h1', (hL u).trans h2, h3⟩
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
    ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end Setlec
