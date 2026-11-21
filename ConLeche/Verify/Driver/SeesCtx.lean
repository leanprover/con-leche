module

public import ConLeche.Verify.Driver.SeesLoads
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Driver.ReachFrom
import ConLeche.Verify.Driver.RouteCtx
import ConLeche.Verify.Driver.RouteWorker

/-!
# What a module sees, against its context (task #618)

At a module `M` of an accepted run, a name `M` sees as `m'`'s (`Sees`):

* is no own record's name: a name `M`'s own environment stores and `M` sees is in its context
  (`Run.sees_ctx`; the worker's freshness: no name of `M`'s private view is loaded);
* is seen from one module only, where `M`'s context does not store it (`Run.sees_unique`): two
  loaded copies of one name from two modules make a clash, and every clash's name is a root of
  the reach, so stored in the context;
* agrees with `m'`'s copy where the context stores it (`Run.sees_agree`, `agree_loaded`).
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend.Olean

/-- **`clashAgree` returns the name of every clash with a copy in the index**, and keeps what it
has gathered. -/
theorem clashAgree_names (env : ReachEnv ModelIO) (fs : FS) :
    ∀ (c : ReachCache) (cls : List Clash) (acc : Array Name) {hs₀ : HS},
      ModelIO.AllOk (clashAgree env c cls acc) fs hs₀ fun p => ∀ extra, p.2 = .ok extra →
        (∀ n ∈ acc, n ∈ extra) ∧ ∀ cl ∈ cls,
          (∃ x ∈ cl.copies.toList, (env.wr.index.at x.1).isSome = true) → cl.name ∈ extra
  | c, [], acc, _ => by
    simp only [clashAgree, ModelIO.allOk_pure, Except.ok.injEq]
    rintro extra rfl
    exact ⟨fun n hn => hn, fun cl hcl => nomatch hcl⟩
  | c, cl :: cls, acc, _ => by
    simp only [clashAgree, ModelIO.allOk_bind]
    intro x _ _
    obtain ⟨c', r⟩ := x
    cases r with
    | error e => simp
    | ok ps =>
      simp only []
      split
      · simp
      · split
        · intro v hs' hv extra he
          obtain ⟨h1, h2⟩ := clashAgree_names env fs _ cls _ v hs' hv extra he
          refine ⟨fun n hn => h1 n (Array.mem_push_of_mem _ hn), fun cl' hcl' hc => ?_⟩
          rcases List.mem_cons.1 hcl' with rfl | hcl'
          · exact h1 _ (Array.mem_push_self)
          · exact h2 cl' hcl' hc
        · split
          · intro v hs' hv extra he
            obtain ⟨h1, h2⟩ := clashAgree_names env fs _ cls _ v hs' hv extra he
            refine ⟨fun n hn => h1 n (Array.mem_push_of_mem _ hn), fun cl' hcl' hc => ?_⟩
            rcases List.mem_cons.1 hcl' with rfl | hcl'
            · exact h1 _ (Array.mem_push_self)
            · exact h2 cl' hcl' hc
          · rename_i hsp
            intro v hs' hv extra he
            obtain ⟨h1, h2⟩ := clashAgree_names env fs _ cls _ v hs' hv extra he
            refine ⟨h1, fun cl' hcl' hc => ?_⟩
            rcases List.mem_cons.1 hcl' with rfl | hcl'
            · exfalso
              obtain ⟨⟨cp, cv, k⟩, hx, hat⟩ := hc
              obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hat
              rw [List.filterMap_eq_nil_iff] at hsp
              have := hsp _ hx
              simp only at hq
              simp [hq] at this
            · exact h2 cl' hcl' hc

/-- **Every clash with a copy in the index, of a name that is not own, is stored in the
context**: `clashAgree` makes its name a root of the reach. -/
theorem reach_clash {rd : OleanReads ModelIO} {m : Name} {wr : WorkerReads}
    {own : Std.HashSet Name} {roots : Array Name} {fs : FS} {r : Reach} {hs hs' : HS}
    {fl : FlagInfer} (h : (reachWith fl rd m wr own roots : ModelIO _) fs hs (.ok (.ok r)) hs') {cl : Clash}
    (hcl : cl ∈ wr.clashes.toList)
    (hcp : ∃ x ∈ cl.copies.toList, (wr.index.at x.1).isSome = true)
    (hown : own.contains cl.name = false) :
    ((streamEnv r.ctx.toList).find? cl.name).isSome = true := by
  unfold reachWith at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨⟨c, x⟩, _, hca, h⟩ := h
  rcases x with e | extra
  · simp at h
  have hex : cl.name ∈ extra :=
    (clashAgree_names _ fs {} wr.clashes.toList #[] _ _ hca extra rfl).2 cl hcl hcp
  simp only at h
  generalize List.find? _ _ = q at h
  cases q with
  | some x => simp at h
  | none =>
    simp only [ModelIO.bind_ok] at h
    obtain ⟨y, _, hy, h⟩ := h
    rcases y with e | ⟨L, c'⟩
    · simp at h
    simp only at h
    cases ho : readOrder L.ctx L.reads with
    | error e => simp [ho] at h
    | ok o =>
    simp only [ho] at h
    cases hv : validateCtx (o.map (L.ctx.getD · default)) (o.map (L.homes.getD · default)) with
    | error e => rw [hv] at h; simp at h
    | ok u =>
    cases hf : fl (o.map (L.ctx.getD · default)).toList c'.pending.toList with
    | error e => rw [hv] at h; simp only at h; rw [hf] at h; simp at h
    | ok u' =>
    simp only [hv, hf, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    subst h
    simp only
    have hperm := readOrder_perm ho
    obtain ⟨d, hd, hxd⟩ := streamEnv_find_mem (reachGo_roots _ fs (reachInv_init _) hy cl.name
      (List.mem_filter.2 ⟨by simp [hex], by simp [hown]⟩))
    exact streamEnv_find_of_mem (hperm.mem_iff.2 hd) hxd

end ConLeche.Driver

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

variable {sp : Roots} {fs : FS} {maxNatSize : Nat}

namespace Run

variable (R : Run sp fs maxNatSize)

/-- **Every passed read agrees, at every module of the run.** -/
theorem agreeAll : ∀ M ∈ R.names, R.AgreeAll M :=
  R.agree_all fun M hM ih b y hPr hy => by
    obtain ⟨h, rfl, hP⟩ := hPr
    obtain ⟨-, -, -, s₁, hs₁, -, -⟩ := R.passed_open hM hP hy
    by_cases hmod : s₁.part.mod = h
    · exact R.route_same hM hP hy hs₁ hmod
    · exact R.route hM ih hP hy hs₁ hmod

/-- **A name a module stores and sees is in its context.** -/
theorem sees_ctx (hl : ∀ M, R.look M = sp) {M : Name}
    (hM : M ∈ R.names) {n m' : Name} (h : SeesX sp fs (R.x M) M n m')
    (hn : ((R.dev (R.rk M)).own.find? n).isSome = true) :
    ((R.dev (R.rk M)).context.find? n).isSome = true := by
  obtain ⟨cp, q, hq, hqn, -⟩ := R.sees_copy hl hM h
  have hf := first_of_at (R.facts M hM) hq
  rw [hqn] at hf
  have hn' : ((ownEnvOf (R.look M) fs M (R.w M)).find? n).isSome = true := by
    rw [R.dev_rk hM] at hn; exact hn
  exact R.stored_of_own_find hM hn' hf

/-- At a compared challenge, a loaded name is no own name. -/
theorem ownNamesOf_loaded {x : Array ImportRec} (hx : x.isEmpty = false) {ix : NameIndex}
    {l : Loaded} {n : Name} (h : (ix.first[n]?).isSome = true) :
    (ownNamesOf x ix l).contains n = false := by
  simp only [ownNamesOf, hx, Bool.false_eq_true, ↓reduceIte]
  rw [← Array.foldl_toList]
  suffices ∀ (cs : List CEntry) (s0 : Std.HashSet Name), s0.contains n = false →
      (cs.foldl (fun s c => if ix.first.contains c.name then s else s.insert c.name) s0).contains
        n = false from this _ _ (by simp)
  intro cs
  induction cs with
  | nil => intro s0 h0; exact h0
  | cons c cs ih =>
    intro s0 h0
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h0
    · rename_i hc
      rw [Std.HashSet.contains_insert]
      simp only [Bool.or_eq_false_iff]
      refine ⟨?_, h0⟩
      simp only [beq_eq_false_iff_ne]
      rintro rfl
      simp only [Std.HashMap.contains_eq_isSome_getElem?] at hc
      exact hc h

/-- **Outside the context, a name is seen from one module only.** -/
theorem sees_unique (hl : ∀ M, R.look M = sp) {M : Name}
    (hM : M ∈ R.names) {n m₁ m₂ : Name} (h₁ : SeesX sp fs (R.x M) M n m₁)
    (h₂ : SeesX sp fs (R.x M) M n m₂)
    (hn : ((R.dev (R.rk M)).context.find? n).isSome = false) : m₁ = m₂ := by
  obtain ⟨cp₁, q₁, hq₁, hn₁, rfl⟩ := R.sees_copy hl hM h₁
  obtain ⟨cp₂, q₂, hq₂, hn₂, rfl⟩ := R.sees_copy hl hM h₂
  refine Classical.byContradiction fun hne => ?_
  have hcp : cp₁ ≠ cp₂ := fun e => hne (by rw [e])
  have hw := R.facts M hM
  obtain ⟨_, _, hr⟩ := hw.reads
  obtain ⟨cl, hcl, hcln, ⟨cv, kd, hmem⟩, -⟩ := workerClash_complete hr hcp hq₁ hq₂ hn₁ hn₂
  -- the clash's name is loaded, so no own name
  have hf := first_of_at hw hq₁
  rw [hn₁] at hf
  have hown : (ownOf (R.x M) (R.w M)).contains cl.name = false := by
    rw [hcln]
    by_cases hx : R.x M = #[]
    · show (ownNamesOf (R.x M) _ (R.w M).home).contains n = false
      rw [hx]
      show (ownNames (R.w M).home).contains n = false
      cases hc : (ownNames (R.w M).home).contains n
      · rfl
      · rw [first_none_of_ownNames (R.facts₀ hM hx) hc] at hf; cases hf
    · have hxe : (R.x M).isEmpty = false := by
        cases hxe : (R.x M).isEmpty
        · rfl
        · exact absurd (Array.isEmpty_iff.1 hxe) hx
      exact ownNamesOf_loaded hxe hf
  obtain ⟨_, _, _, _, hreach⟩ := (R.facts M hM).reach
  have := reach_clash hreach hcl ⟨_, hmem, by rw [hq₁]; rfl⟩ hown
  rw [hcln] at this
  rw [R.dev_rk hM] at hn
  have hn' : ((streamEnv (R.w M).reach.ctx.toList).find? n).isSome = false := hn
  rw [this] at hn'
  cases hn'

/-- **A context name agrees with every copy the module sees.** -/
theorem sees_agree (hl : ∀ M, R.look M = sp) {M : Name}
    (hM : M ∈ R.names) {n m' : Name} (h : SeesX sp fs (R.x M) M n m')
    (hn : ((R.dev (R.rk M)).context.find? n).isSome = true) :
    Agree R.dev (R.rk M) (R.rk m') n := by
  obtain ⟨cp, q, hq, hqn, rfl⟩ := R.sees_copy hl hM h
  exact R.agree_loaded hM (R.agreeAll M hM) hn hq hqn

end Run

end ConLeche.Driver.Compose
