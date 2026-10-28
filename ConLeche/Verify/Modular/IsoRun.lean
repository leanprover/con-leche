module

public import ConLeche.Verify.Modular.Dev
public import ConLeche.Verify.Modular.IsoCtx
public import ConLeche.Verify.Modular.IsoFast
import ConLeche.Verify.Modular.Congr
import ConLeche.Verify.Modular.Scope

public section

/-!
# The isolated run and the store run establish the same (task #373)

A modular run in **store mode** installs and checks every module at its
view of one store and establishes `RunOk`.  A run in **isolated mode**
checks every module in an environment of its own, built from its
imports' units alone (`isoCtx`), and establishes `IsoRunOk`: the same
facts with the install, the record checks and the proofs' checks done
in that environment.  The bookkeeping of the two (the units, their
checks `unitOk`, the local checks `localOk`, the list of names stored
twice) is the same, and so are the units: in isolated mode a module's
view is rebuilt from its own constants (`ownView`).

* `IsoRunOk.runOk` and `RunOk.isoRunOk` — each establishes the other
  (for the same store and units; the store run's records' check list,
  whose bounds count from the view's zero, is recovered by the
  equivalence of the folds), given that the name index lists every unit
  constant (`IdxOk`, part of `IsoRunOk`, decided by every run);
* `isoDevOf` — the development an isolated run stands for: every
  module's context is the one built from its imports' units, its own
  environment its constants over that context; the rest (sources,
  proofs, qualified names, interfaces) as the store run's (`devOf`);
* **`IsoRunOk.localOk`** — every module of it passes the local checks,
  the hypothesis of the modular capstones `ConLeche.modular_model_exists`
  and `ConLeche.modular_no_False`; and `RunOk.localOk_iso`, the same for
  a store run.
-/

namespace ConLeche.Cached.Mod

open ConLeche ConLeche.Modular

variable {mode : CheckMode} {S : Store} {M : Array ModData}

/-! ## The isolated development -/

/-- **Module `i` checked in isolation**: its context built from its
imports' units, its own environment its installed constants over it. -/
@[expose] def isoModuleOf (S : Store) (i : Nat) (d : ModData) : Module :=
  { moduleOf S i d with context := isoCtx S.slot (S.lvl i),
                        own := Env.over d.fe.env (isoCtx S.slot (S.lvl i)) }

/-- **The development an isolated run stands for.** -/
@[expose] def isoDevOf (S : Store) (M : Array ModData) (i : Nat) : Module :=
  if h : i < M.size then isoModuleOf S i M[i] else emptyModule

/-! ## What an isolated run establishes -/

/-- **What an isolated modular run establishes**: as `RunOk`, but every
module's records installed from the canonical index of its context
built from its imports' units — every record checked there, its proofs
attested there, its own constants and tables those its data holds over
that context — and its data's view the canonical index of its own
constants over the store (`ownView`, what the unit's check reads); and
the store's name index lists every unit constant (`IdxOk`). -/
structure IsoRunOk (mode : CheckMode) (S : Store) (M : Array ModData) : Prop where
  slots : S.slots.size = M.size
  lvls : ∀ i, i < M.size → (S.lvl i).size = M.size
  below : ∀ i (h : i < M.size), ∀ b ∈ M[i].imports, b < i
  idx : IdxOk S
  iso : ∀ i (h : i < M.size), ∃ n feI pendI,
    InstallRun mode natOpPinSets M[i].ds.toList (0, mkFEnv (isoCtx S.slot (S.lvl i)), #[])
      (n, feI, pendI) ∧
    (∀ pc ∈ pendI.toList, ∃ s, checkPending mode feI pc {} = .ok ((), s)) ∧
    ProofsAttested mode M[i].flags.contains feI pendI ∧
    feI.env = Env.over M[i].fe.env (isoCtx S.slot (S.lvl i))
  view : ∀ i (h : i < M.size), M[i].fe = ownView M[i].fe.env (S.mb i)
  slot : ∀ i (h : i < M.size), S.slot i = M[i].unit.slot
  priv : ∀ i (h : i < M.size), M[i].unit.slot.prv.priv = M[i].fe.env.consts.reverse.toArray
  unit : ∀ i (h : i < M.size), unitOk S i M[i].fe M[i].flags.contains M[i].unit M[i].reads = true
  locals : ∀ i, i < M.size → localOk S (M.map (·.unit)) i = true
  dups : dupsOk S = true

/-- **Every module of an isolated run passes its isolated check**: the
declaration fold from its context built from its imports' units
accepts, with its own constants and tables over that context. -/
theorem IsoRunOk.checks (h : IsoRunOk mode S M) (i : Nat) (hi : i < M.size) :
    checkModuleIsolated mode natOpPinSets S.slot (S.lvl i) M[i].ds =
      .ok (Env.over M[i].fe.env (isoCtx S.slot (S.lvl i))) := by
  obtain ⟨n, feI, pendI, hrun, hchk, -, henv⟩ := h.iso i hi
  unfold checkModuleIsolated checkDeclsAt isoIndex
  rw [← Array.foldlM_toList, hrun.foldlM]
  show (checkPendingList mode feI pendI.toList >>= fun _ => pure feI.env) = _
  rw [checkPendingList_ok mode feI pendI.toList hchk, henv]
  rfl

/-! ## An install from a context only conses onto it -/

theorem Twin.refl' {fe : FEnv} (h : IdxBelow fe) : Twin fe fe := ⟨rfl, rfl, h, h⟩

/-- A run of the fold's steps only conses constants and tables onto its
start's. -/
theorem _root_.ConLeche.Cached.InstallRun.extends {pins : List NatOpPinSet} {ds : List Declaration}
    {p q : Nat × FEnv × Array PendingCheck} (hrun : InstallRun mode pins ds p q)
    (hp : IdxBelow p.2.1) :
    ∃ L Q, q.2.1.env = ⟨L ++ p.2.1.env.consts, Q ++ p.2.1.env.tables⟩ := by
  induction hrun with
  | nil p => exact ⟨[], [], rfl⟩
  | @cons d ds p p₁ q hstep rest ih =>
    obtain ⟨i, fe, pend⟩ := p
    obtain ⟨L, Q, vg?, rfl, -, -⟩ := installDeclStep_twin (pend₂ := pend) (Twin.refl' hp) hstep
    obtain ⟨L', Q', he⟩ := ih (hp.pushDelta L Q)
    refine ⟨L' ++ L.reverse, Q' ++ Q.reverse, ?_⟩
    rw [he, pushDelta_env]
    simp

/-- **An install from a context's canonical index ends over the
context**: its environment is its own part (`ownPart`) over it. -/
theorem _root_.ConLeche.Cached.InstallRun.over_ctx {pins : List NatOpPinSet} {ds : List Declaration} {C : Env}
    {n : Nat} {fe : FEnv} {pend : Array PendingCheck}
    (hrun : InstallRun mode pins ds (0, mkFEnv C, #[]) (n, fe, pend)) :
    fe.env = Env.over (ownPart C fe.env) C := by
  obtain ⟨L, Q, he⟩ := hrun.extends (IdxBelow.mkFEnv C)
  have hc : (mkFEnv C).env = C := rfl
  rw [hc] at he
  rw [he]
  unfold ownPart Env.over
  simp only [List.length_append, Nat.add_sub_cancel, List.take_left]

/-! ## From one mode's evidence to the other's -/

theorem shiftPC_vg (k : Nat) (pc : PendingCheck) : (shiftPC k pc).vg = pc.vg := rfl

theorem shiftPC_thm (k : Nat) (pc : PendingCheck) :
    { shiftPC k pc with vg := { (shiftPC k pc).vg with kind := .thm } } =
      shiftPC k { pc with vg := { pc.vg with kind := .thm } } := rfl

/-- The proofs a run's records attest, at the view or over the context
(the same records, their bounds shifted). -/
theorem attested_over {mb : MBase} {C : Env} (hC : BaseLike C mb) {fe : FEnv}
    (hfe : CanonB fe { mb := some mb }) {proofs : Name → Bool} {pend : Array PendingCheck} :
    ProofsAttested mode proofs fe pend ↔
      ProofsAttested mode proofs (ConLeche.mkFEnv (envAt fe C))
        (pend.map (shiftPC C.consts.length)) := by
  constructor
  · intro h n hn
    obtain ⟨pc, hpc, hname, hpin, hk⟩ := h n hn
    refine ⟨shiftPC C.consts.length pc, ?_, hname, hpin, ?_⟩
    · rw [Array.toList_map]; exact List.mem_map_of_mem hpc
    · rcases hk with hk | ⟨hk, s, hs⟩
      · exact .inl hk
      · refine .inr ⟨hk, s, ?_⟩
        rw [shiftPC_thm, checkPending_over hC hfe]; exact hs
  · intro h n hn
    obtain ⟨pc', hpc', hname, hpin, hk⟩ := h n hn
    rw [Array.toList_map] at hpc'
    obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hpc'
    refine ⟨pc, hpc, hname, hpin, ?_⟩
    rcases hk with hk | ⟨hk, s, hs⟩
    · exact .inl hk
    · refine .inr ⟨hk, s, ?_⟩
      rw [shiftPC_thm, checkPending_over hC hfe] at hs; exact hs

/-- The checks of a run's records, at the view or over the context. -/
theorem checked_over {mb : MBase} {C : Env} (hC : BaseLike C mb) {fe : FEnv}
    (hfe : CanonB fe { mb := some mb }) {pend : Array PendingCheck} :
    (∀ pc ∈ pend.toList, ∃ s, checkPending mode fe pc {} = .ok ((), s)) ↔
      (∀ pc ∈ (pend.map (shiftPC C.consts.length)).toList,
        ∃ s, checkPending mode (ConLeche.mkFEnv (envAt fe C)) pc {} = .ok ((), s)) := by
  constructor
  · intro h pc' hpc'
    rw [Array.toList_map] at hpc'
    obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hpc'
    rw [checkPending_over hC hfe]; exact h pc hpc
  · intro h pc hpc
    have := h (shiftPC C.consts.length pc) (by rw [Array.toList_map]; exact List.mem_map_of_mem hpc)
    rw [checkPending_over hC hfe] at this; exact this

theorem CanonB.eq_ownView {fe : FEnv} {mb : MBase} (h : CanonB fe { mb := some mb }) :
    fe = ownView fe.env mb := h

/-- **A store run is an isolated run**: every module's view install,
checks and proofs are its isolated install, checks and proofs (the
same constants, the same verdicts), when the name index lists every
unit constant. -/
theorem RunOk.isoRunOk (hR : RunOk mode S M) (hI : IdxOk S) : IsoRunOk mode S M := by
  refine { slots := hR.slots, lvls := hR.lvls, below := hR.below, idx := hI, iso := ?_,
           view := ?_, slot := hR.slot, priv := hR.priv, unit := hR.unit, locals := hR.locals,
           dups := hR.dups }
  · intro i hi
    have hC := baseLike_isoCtx hI i
    obtain ⟨n, hrun⟩ := hR.run i hi
    obtain ⟨hf, hq⟩ := foldlM_over (mode := mode) (pins := natOpPinSets) hC M[i].ds.toList
      (0, viewOf (S.mb i), #[]) (canonB_viewOf _)
    have hv : M[i].ds.toList.foldlM (installDeclStep mode natOpPinSets) (0, viewOf (S.mb i), #[]) =
        .ok (n, M[i].fe, M[i].pend) := hrun.foldlM
    have hcan : CanonB M[i].fe { mb := some (S.mb i) } := hq _ hv
    rw [hv] at hf
    have h0 : overState (isoCtx S.slot (S.lvl i)) (0, viewOf (S.mb i), #[]) =
        (0, mkFEnv (isoCtx S.slot (S.lvl i)), #[]) := by
      unfold overState; rw [envAt_viewOf_over]; simp
    rw [h0] at hf
    refine ⟨n, _, _, InstallRun.of_foldlM mode _ _ hf, ?_, ?_, rfl⟩
    · exact (checked_over hC hcan).mp (hR.chk i hi)
    · exact (attested_over hC hcan).mp (hR.prf i hi)
  · intro i hi
    obtain ⟨n, hrun⟩ := hR.run i hi
    obtain ⟨-, hq⟩ := foldlM_over (mode := mode) (pins := natOpPinSets)
      (baseLike_ctxOf (S.mb i)) M[i].ds.toList (0, viewOf (S.mb i), #[]) (canonB_viewOf _)
    have hv : M[i].ds.toList.foldlM (installDeclStep mode natOpPinSets) (0, viewOf (S.mb i), #[]) =
        .ok (n, M[i].fe, M[i].pend) := hrun.foldlM
    exact CanonB.eq_ownView (hq _ hv)

/-- The view's records of an isolated module: the store run's install,
checks and proofs at the view, recovered from the isolated ones. -/
theorem IsoRunOk.viewRun (h : IsoRunOk mode S M) (i : Nat) (hi : i < M.size) :
    ∃ n pend, InstallRun mode natOpPinSets M[i].ds.toList (0, S.view i, #[]) (n, M[i].fe, pend) ∧
      (∀ pc ∈ pend.toList, ∃ s, checkPending mode M[i].fe pc {} = .ok ((), s)) ∧
      ProofsAttested mode M[i].flags.contains M[i].fe pend := by
  have hC := baseLike_isoCtx h.idx i
  obtain ⟨n, feI, pendI, hrun, hchk, hprf, henv⟩ := h.iso i hi
  obtain ⟨hf, hq⟩ := foldlM_over (mode := mode) (pins := natOpPinSets) hC M[i].ds.toList
    (0, viewOf (S.mb i), #[]) (canonB_viewOf _)
  have h0 : overState (isoCtx S.slot (S.lvl i)) (0, viewOf (S.mb i), #[]) =
      (0, mkFEnv (isoCtx S.slot (S.lvl i)), #[]) := by
    unfold overState; rw [envAt_viewOf_over]; simp
  rw [h0, hrun.foldlM] at hf
  cases hv : M[i].ds.toList.foldlM (installDeclStep mode natOpPinSets) (0, viewOf (S.mb i), #[]) with
  | error e => rw [hv] at hf; exact nomatch hf
  | ok q =>
    rw [hv] at hf
    obtain ⟨n', fe₁, pend₁⟩ := q
    have hcan : CanonB fe₁ { mb := some (S.mb i) } := hq _ hv
    simp only [Except.map, overState, Except.ok.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, hfe, hpend⟩ := hf
    -- the view's final index is the module's data's
    have he : fe₁.env = M[i].fe.env := by
      have h1 : (ConLeche.mkFEnv (envAt fe₁ (isoCtx S.slot (S.lvl i)))).env = feI.env := by rw [hfe]
      rw [henv] at h1
      have h2 : envAt fe₁ (isoCtx S.slot (S.lvl i)) =
          Env.over M[i].fe.env (isoCtx S.slot (S.lvl i)) := h1
      unfold envAt Env.over at h2
      simp only [Env.mk.injEq] at h2
      have hc := List.append_cancel_right h2.1
      have ht := List.append_cancel_right h2.2
      cases h3 : fe₁.env
      cases h4 : M[i].fe.env
      rw [h3] at hc ht; rw [h4] at hc ht
      simp_all
    have hfe₁ : fe₁ = M[i].fe := by
      rw [hcan.eq_ownView, h.view i hi, he]
    subst hfe₁
    subst hfe
    subst hpend
    refine ⟨n, pend₁, InstallRun.of_foldlM mode _ _ hv, ?_, ?_⟩
    · exact (checked_over hC hcan).mpr hchk
    · exact (attested_over hC hcan).mpr hprf

/-- **An isolated run is a store run** of the same store and units: the
view's records' check list, recovered module by module, completes the
evidence; nothing the development reads changes. -/
theorem IsoRunOk.runOk (h : IsoRunOk mode S M) :
    ∃ M' : Array ModData, RunOk mode S M' ∧ ∀ k, devOf S M' k = devOf S M k := by
  classical
  let pf : (i : Nat) → i < M.size → Array PendingCheck := fun i hi =>
    Classical.choose (Classical.choose_spec (h.viewRun i hi))
  have hpf : ∀ i (hi : i < M.size), ∃ n, InstallRun mode natOpPinSets M[i].ds.toList
      (0, S.view i, #[]) (n, M[i].fe, pf i hi) ∧
      (∀ pc ∈ (pf i hi).toList, ∃ s, checkPending mode M[i].fe pc {} = .ok ((), s)) ∧
      ProofsAttested mode M[i].flags.contains M[i].fe (pf i hi) := fun i hi =>
    ⟨_, Classical.choose_spec (Classical.choose_spec (h.viewRun i hi))⟩
  let M' : Array ModData := Array.ofFn fun k : Fin M.size => { M[k] with pend := pf k k.2 }
  have hsz : M'.size = M.size := Array.size_ofFn
  have hget : ∀ i (hi : i < M'.size), M'[i] = { M[i]'(hsz ▸ hi) with pend := pf i (hsz ▸ hi) } :=
    fun i hi => Array.getElem_ofFn ..
  have hunits : M'.map (·.unit) = M.map (·.unit) := by
    apply Array.ext (by simp [hsz])
    intro k h₁ h₂
    simp only [Array.getElem_map]
    rw [hget k (by simpa using h₁)]
  refine ⟨M', ?_, fun k => ?_⟩
  · refine { slots := hsz ▸ h.slots, lvls := fun i hi => hsz ▸ h.lvls i (hsz ▸ hi),
             below := fun i hi => by rw [hget]; exact h.below i _,
             run := fun i hi => ?_, chk := fun i hi => ?_, prf := fun i hi => ?_,
             slot := fun i hi => by rw [hget]; exact h.slot i _,
             priv := fun i hi => by rw [hget]; exact h.priv i _,
             unit := fun i hi => by rw [hget]; exact h.unit i _,
             locals := fun i hi => by rw [hunits]; exact h.locals i (hsz ▸ hi),
             dups := h.dups }
    · rw [hget]; obtain ⟨n, r, -, -⟩ := hpf i (hsz ▸ hi); exact ⟨n, r⟩
    · rw [hget]; exact (hpf i (hsz ▸ hi)).choose_spec.2.1
    · rw [hget]; exact (hpf i (hsz ▸ hi)).choose_spec.2.2
  · unfold devOf
    by_cases hk : k < M.size
    · have hk' : k < M'.size := hsz ▸ hk
      simp only [hk, hk', ↓reduceDIte]
      rw [hget k hk']
      rfl
    · have hk' : ¬ k < M'.size := hsz ▸ hk
      simp only [hk, hk', ↓reduceDIte]

/-! ## The local checks of the isolated development -/

theorem isoDevOf_eq (S : Store) (M : Array ModData) (k : Nat) :
    isoDevOf S M k =
      { devOf S M k with context := (isoDevOf S M k).context, own := (isoDevOf S M k).own } := by
  unfold isoDevOf devOf
  split <;> rfl

theorem env_over_nil (C : Env) : C = Env.over ⟨[], []⟩ C := by
  cases C; rfl

/-- **Every module of an isolated run passes its local checks** in the
development the run stands for — contexts built from the imports' units,
own environments over them: the hypothesis of the modular capstones
(`ConLeche.modular_model_exists`, `ConLeche.modular_no_False`). -/
theorem IsoRunOk.localOk (h : IsoRunOk mode S M) (i : Nat) :
    LocalOk mode natOpPinSets (isoDevOf S M) i := by
  obtain ⟨M', hR, hdev⟩ := h.runOk
  have h₁ : LocalOk mode natOpPinSets (devOf S M) i := by
    have := hR.localOk i
    rwa [show devOf S M' = devOf S M from funext hdev] at this
  have hctx : ∀ k, EnvLike (devOf S M k).context (isoDevOf S M k).context := by
    intro k
    unfold devOf isoDevOf
    split
    · exact EnvLike.of_base (baseLike_ctxOf _) (baseLike_isoCtx h.idx k)
    · exact EnvLike.refl _
  have hown : ∀ k, EnvLike (devOf S M k).own (isoDevOf S M k).own := by
    intro k
    unfold devOf isoDevOf
    split
    · exact (EnvLike.of_base (baseLike_ctxOf _) (baseLike_isoCtx h.idx k)).over _
    · exact EnvLike.refl _
  refine LocalOk.congr _ _ (isoDevOf_eq S M) hctx hown ?_ ?_ ?_ ?_ h₁
  · unfold isoDevOf
    split
    · exact isoCtx_nodup _ _
    · exact List.nodup_nil
  · unfold isoDevOf
    split
    · exact isoCtx_tables_mem _ _
    · intro t ht; cases ht
  · unfold isoDevOf devOf
    split
    · intro hacc
      have hC := EnvLike.of_base (baseLike_ctxOf (S.mb i)) (baseLike_isoCtx h.idx i)
      have := AcceptedFrom.over_congr hC hacc ⟨[], []⟩ M[i].fe.env (env_over_nil _) rfl
      rwa [← env_over_nil] at this
    · exact id
  · unfold isoDevOf
    split
    · intro hc; cases hc
    · intro hc; cases hc

/-- **Every module of a store run passes its local checks in the isolated
development too**: the store run is an isolated run (`RunOk.isoRunOk`). -/
theorem RunOk.localOk_iso (hR : RunOk mode S M) (hI : IdxOk S) (i : Nat) :
    LocalOk mode natOpPinSets (isoDevOf S M) i :=
  (hR.isoRunOk hI).localOk i

end ConLeche.Cached.Mod
