import Setlec.Kernel.ArenaWF
import Setlec.Kernel.Core
import Setlec.Verify.AbstractRange
import Setlec.Verify.Subst

/-!
# Verification of the interned expression arena: the operations

The arena *data structure* verification — `denote`, `EStore.WF`, the
`intern*` preservation/round-trip lemmas, canonicity, and the eager
derived-field exactness facts — lives in `Setlec/Kernel/ArenaWF.lean`
(self-contained, importable by the implementation layer; task #103).
This module adds the lemmas connecting the arena *operations* of
`Setlec/Kernel/IExpr.lean` to their `Expr` counterparts: each syntactic
operation commutes with `denote`, and the pure queries agree with the
`Expr` versions.

Progress (stage 1 tracking):
* [x] `children` / `denoteNode` / `denote` (in `ArenaWF`)
* [x] `EStore.WF`, `EStore.Ext`, `denote_mono` (in `ArenaWF`)
* [x] `intern` preserves `WF`; `internExpr` round-trips (in `ArenaWF`)
* [x] canonicity: `denote_inj` / `denote_eq_iff` (in `ArenaWF`)
* [x] `instantiate1I` commutes with `denote`
* [x] `abstract1I`, `instantiateLevelParamsI` commute with `denote`
* [x] pure queries (`hasFvarI`, `looseBVarsBoundedI`, `wscopedBI`,
      `fvarLeavesI`, `constsResolveI`) agree with the `Expr` versions
-/

namespace Setlec

namespace EStore

/-! ## The memo invariant for the index→index traversals -/

/-- Invariant of a per-call memo table for an index→index traversal with
a `Nat` cursor implementing the expression function `g`: every entry's
key is in range and maps denotation-consistently.  (Entries for in-range
keys that do not denote are permanently vacuous: an in-range index's
denotation never changes under extension.) -/
def MemoNInv (st : EStore) (g : Expr → Nat → Expr)
    (memo : Std.HashMap (EIdx × Nat) EIdx) : Prop :=
  ∀ (e : EIdx) (c : Nat) (r : EIdx), memo[(e, c)]? = some r →
    e < st.nodes.size ∧ ∀ x, st.denote e = some x → st.denote r = some (g x c)

theorem MemoNInv.empty {st : EStore} {g : Expr → Nat → Expr} :
    MemoNInv st g {} := by
  intro e c r hr
  simp at hr

theorem MemoNInv.mono {st st' : EStore} {g : Expr → Nat → Expr}
    {memo : Std.HashMap (EIdx × Nat) EIdx} (hext : Ext st st') (hwf : st.WF)
    (h : MemoNInv st g memo) : MemoNInv st' g memo := by
  intro e c r hr
  obtain ⟨hlt, hcond⟩ := h e c r hr
  refine ⟨Nat.lt_of_lt_of_le hlt hext.size_le, ?_⟩
  intro x hx
  rw [hext.denote_eq_of_lt hwf hlt] at hx
  exact denote_mono hext (hcond x hx)

theorem MemoNInv.insert {st : EStore} {g : Expr → Nat → Expr}
    {memo : Std.HashMap (EIdx × Nat) EIdx} {e : EIdx} {c : Nat} {r : EIdx}
    (h : MemoNInv st g memo) (hlt : e < st.nodes.size)
    (hcond : ∀ x, st.denote e = some x → st.denote r = some (g x c)) :
    MemoNInv st g (memo.insert (e, c) r) := by
  intro e' c' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : (e, c) = (e', c')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact ⟨hlt, hcond⟩
  · rw [if_neg (by simpa using hk)] at hr'
    exact h e' c' r' hr'

/-- Transport a "old-store input, new-store output" condition to the new
store (the input's denotation is unchanged below the old size). -/
theorem cond_transport {st st' : EStore} (hext : Ext st st') (hwf : st.WF)
    {e r : EIdx}
    (hesz : e < st.nodes.size) {g : Expr → Expr}
    (hcond : ∀ x, st.denote e = some x → st'.denote r = some (g x)) :
    ∀ x, st'.denote e = some x → st'.denote r = some (g x) := by
  intro x hx
  rw [hext.denote_eq_of_lt hwf hesz] at hx
  exact hcond x hx


/-- `fvarRange` is exact for `fvarsBelow`. -/
theorem fvarsBelow_iff {x : Expr} {d : Nat} :
    x.fvarsBelow d ↔ x.fvarRange ≤ d := by
  induction x <;>
    (try simp [Expr.fvarsBelow, Expr.fvarRange, Nat.max_le, *]) <;>
    omega


/-- Cutoff consequence: a range entry at or below the base certifies
`fvarsBelow` of the denotation (the abstraction traversals' identity
branch). -/
theorem WF.fvarRangeD_le {st : EStore} (hwf : st.WF) {e : EIdx}
    {x : Expr} {d : Nat} (hx : st.denote e = some x)
    (hle : st.fvarRangeD e ≤ d) : x.fvarsBelow d :=
  fvarsBelow_iff.mpr (hwf.fvarRangeD_exact e hx ▸ hle)

/-! ## `instantiate1I` commutes with `denote` -/

/-- Correctness of the memoized traversal core: on a well-formed store,
`instantiate1IGo` preserves the invariant, extends the store, keeps the
memo consistent, and its result denotes `Expr.instantiate1` of the
input's denotation. -/
theorem instantiate1IGo_spec {v : EIdx} {w : Expr} :
    ∀ (e : EIdx) {st : EStore} {memo : MemoN} {d : Nat} {r : EIdx}
      {st' : EStore} {memo' : MemoN},
      st.WF → st.denote v = some w →
      MemoNInv st (fun x c => x.instantiate1 w c) memo →
      instantiate1IGo v st memo e d = (r, st', memo') →
      st'.WF ∧ Ext st st' ∧
        MemoNInv st' (fun x c => x.instantiate1 w c) memo' ∧
        ∀ x, st.denote e = some x → st'.denote r = some (x.instantiate1 w d) := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro st memo d r st' memo' hwf hv hinv hgo
    unfold instantiate1IGo at hgo
    split at hgo
    · -- per-node bound cutoff: no loose bvar at or above the cursor
      rename_i hcut
      cases hgo
      refine ⟨hwf, Ext.refl st, hinv, ?_⟩
      intro x hx
      rw [Expr.instantiate1_eq_self (hwf.bvarBoundD_le hx hcut)]
      exact hx
    split at hgo
    · -- memo hit
      rename_i hhit
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, (hinv _ _ _ hhit).2⟩
    · split at hgo
      · -- index out of range: identity, no memo insert
        rename_i hnone
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          split at hgo
          · -- i = d: the replacement
            rename_i hid
            cases hgo
            subst hid
            have hcond : ∀ x, st.denote e = some x →
                st.denote v = some (x.instantiate1 w i) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.instantiate1] using hv
            exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
          · split at hgo
            · -- i > d: lowered bvar, interned
              rename_i hne hgt
              rcases hI : st.intern (.bvar (i - 1)) with ⟨ri, sti⟩
              rw [hI] at hgo
              cases hgo
              have hwfI : (st.intern (.bvar (i - 1))).2.WF :=
                intern_wf hwf (by simp [ENode.children]) (by simp [ENode.levels]) (by simp [ENode.names])
              have hextI : Ext st (st.intern (.bvar (i - 1))).2 := intern_ext _ _
              have hdI : (st.intern (.bvar (i - 1))).2.denote
                    (st.intern (.bvar (i - 1))).1
                  = denoteNode st.denote st.denoteL st.denoteN (.bvar (i - 1)) :=
                intern_denote hwf (by simp [ENode.children])
              rw [hI] at hwfI hextI hdI
              have hcond : ∀ x, st.denote e = some x →
                  sti.denote ri = some (x.instantiate1 w d) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [hdI]
                simp [Expr.instantiate1, denoteNode, hne, hgt]
              refine ⟨hwfI, hextI, ?_, hcond⟩
              exact (hinv.mono hextI hwf).insert
                (Nat.lt_of_lt_of_le hesz hextI.size_le)
                (cond_transport hextI hwf hesz hcond)
            · -- i < d: unchanged
              rename_i hne hngt
              cases hgo
              have hcond : ∀ x, st.denote e = some x →
                  st.denote e = some (x.instantiate1 w d) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp [Expr.instantiate1, hx, hne, hngt]
              exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          cases hgo
          obtain ⟨xt, hxt⟩ := denote_total hwf t
            (Nat.lt_trans (hcl t (by simp [ENode.children])) hesz)
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.fvar idx nmv xt) := by
            rw [hde, denoteNode, hxt, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiate1 w d) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiate1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiate1 w d) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiate1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun u hu => hwf.levels_lt e _ hn u (by simp [ENode.levels, hu]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiate1 w d) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiate1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiate1 w d) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiate1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiate1IGo v st memo f d with ⟨f', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiate1IGo v st₁ memo₁ a d with ⟨a', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.app f' a') with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih f hguard.1 hwf hv hinv h₁
            have hv₁ := denote_mono hext₁ hv
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih a hguard.2 hwf₁ hv₁ hinv₁ h₂
            have hf₂ : st₂.denote f' = some (xf.instantiate1 w d) :=
              denote_mono hext₂ (hden₁ xf hf)
            have ha₂ : st₂.denote a' = some (xa.instantiate1 w d) :=
              hden₂ xa (denote_mono hext₁ ha)
            have hcI : ∀ c ∈ (ENode.app f' a').children, c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size hf₂
              · exact denote_lt_size ha₂
            have hwf₃ : (st₂.intern (.app f' a')).2.WF :=
              intern_wf hwf₂ hcI (by simp [ENode.levels]) (by simp [ENode.names])
            have hext₃ : Ext st₂ (st₂.intern (.app f' a')).2 := intern_ext _ _
            have hdI := intern_denote (n := .app f' a') hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hf₂, ha₂]
              simp [Expr.instantiate1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiate1IGo v st memo ty d with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiate1IGo v st₁ memo₁ body (d + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.lam nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hv hinv h₁
            have hv₁ := denote_mono hext₁ hv
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hv₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.instantiate1 w d) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.instantiate1 w (d + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.lam nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.lam nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.lam nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.lam nm ty' body' m)).2 := intern_ext _ _
            have hdI := intern_denote (n := .lam nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.instantiate1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiate1IGo v st memo ty d with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiate1IGo v st₁ memo₁ body (d + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.forallE nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hv hinv h₁
            have hv₁ := denote_mono hext₁ hv
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hv₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.instantiate1 w d) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.instantiate1 w (d + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.forallE nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.forallE nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.forallE nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.forallE nm ty' body' m)).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .forallE nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.instantiate1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiate1IGo v st memo ty d with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiate1IGo v st₁ memo₁ val d with ⟨val', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : instantiate1IGo v st₂ memo₂ body (d + 1) with ⟨body', st₃, memo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.letE nm ty' val' body') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hv hinv h₁
            have hv₁ := denote_mono hext₁ hv
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ :=
              ih val hguard.2.1 hwf₁ hv₁ hinv₁ h₂
            have hv₂ := denote_mono hext₂ hv₁
            obtain ⟨hwf₃, hext₃, hinv₃, hden₃⟩ :=
              ih body hguard.2.2 hwf₂ hv₂ hinv₂ h₃
            have ht₃ : st₃.denote ty' = some (xt.instantiate1 w d) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hvv₃ : st₃.denote val' = some (xv.instantiate1 w d) :=
              denote_mono hext₃ (hden₂ xv (denote_mono hext₁ hvv))
            have hb₃ : st₃.denote body' = some (xb.instantiate1 w (d + 1)) :=
              hden₃ xb (denote_mono hext₂ (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.letE nm ty' val' body').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hvv₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.letE nm ty' val' body')).2.WF :=
              intern_wf hwf₃ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.letE nm ty' val' body')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .letE nm ty' val' body') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hvv₃, hb₃,
                denoteN_mono (hext₁.trans (hext₂.trans hext₃)) hnm]
              simp [Expr.instantiate1]
            refine ⟨hwf₄, hextAll, ?_, hcond⟩
            exact (hinv₃.mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : instantiate1IGo v st memo sub d with ⟨sub', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.intern (.proj s j sub') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih sub hguard hwf hv hinv h₁
            have hs₁ : st₁.denote sub' = some (xs.instantiate1 w d) := hden₁ xs hs
            have hcI : ∀ c ∈ (ENode.proj s j sub').children,
                c < st₁.nodes.size := by
              simpa [ENode.children] using denote_lt_size hs₁
            have hwf₂ : (st₁.intern (.proj s j sub')).2.WF := intern_wf hwf₁ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  hext₁.nsize_le)
            have hext₂ : Ext st₁ (st₁.intern (.proj s j sub')).2 := intern_ext _ _
            have hdI := intern_denote (n := .proj s j sub') hwf₁ hcI
            rw [h₂] at hwf₂ hext₂ hdI
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denote e = some x →
                st₂.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hs₁, denoteN_mono hext₁ hnm]
              simp [Expr.instantiate1]
            refine ⟨hwf₂, hextAll, ?_, hcond⟩
            exact (hinv₁.mono hext₂ hwf₁).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)

/-- `instantiate1I` commutes with `denote`: the result denotes
`Expr.instantiate1` of the inputs' denotations, on an extended
well-formed store. -/
theorem instantiate1I_spec {st : EStore} {e v : EIdx} {d : Nat} {a w : Expr}
    (hwf : st.WF) (he : st.denote e = some a) (hv : st.denote v = some w) :
    (st.instantiate1I e v d).2.WF ∧ Ext st (st.instantiate1I e v d).2 ∧
      (st.instantiate1I e v d).2.denote (st.instantiate1I e v d).1
        = some (a.instantiate1 w d) := by
  rcases hgo : instantiate1IGo v st {} e d with ⟨r, st', memo'⟩
  obtain ⟨hwf', hext', -, hcond⟩ :=
    instantiate1IGo_spec e hwf hv MemoNInv.empty hgo
  simp only [instantiate1I, hgo]
  exact ⟨hwf', hext', hcond a he⟩

/-! ## `abstract1I` commutes with `denote` -/

theorem abstract1IGo_spec {dd : Nat} :
    ∀ (e : EIdx) {st : EStore} {memo : MemoN} {k : Nat} {r : EIdx}
      {st' : EStore} {memo' : MemoN},
      st.WF →
      MemoNInv st (fun x c => x.abstract1 dd c) memo →
      abstract1IGo dd st memo e k = (r, st', memo') →
      st'.WF ∧ Ext st st' ∧
        MemoNInv st' (fun x c => x.abstract1 dd c) memo' ∧
        ∀ x, st.denote e = some x → st'.denote r = some (x.abstract1 dd k) := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro st memo k r st' memo' hwf hinv hgo
    unfold abstract1IGo at hgo
    split at hgo
    · rename_i hhit
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, (hinv _ _ _ hhit).2⟩
    · split at hgo
      · rename_i hnone
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstract1 dd k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstract1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          obtain ⟨xt, hxt⟩ := denote_total hwf t
            (Nat.lt_trans (hcl t (by simp [ENode.children])) hesz)
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.fvar idx nmv xt) := by
            rw [hde, denoteNode, hxt, hnm]; rfl
          split at hgo
          · -- idx = dd: abstracted to bvar k
            rename_i hid
            rcases hI : st.intern (.bvar k) with ⟨ri, sti⟩
            rw [hI] at hgo
            cases hgo
            have hwfI : (st.intern (.bvar k)).2.WF :=
              intern_wf hwf (by simp [ENode.children]) (by simp [ENode.levels]) (by simp [ENode.names])
            have hextI : Ext st (st.intern (.bvar k)).2 := intern_ext _ _
            have hdI := intern_denote (n := .bvar k) hwf (by simp [ENode.children])
            rw [hI] at hwfI hextI hdI
            have hcond : ∀ x, st.denote e = some x →
                sti.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI]
              simp [Expr.abstract1, denoteNode, hid]
            refine ⟨hwfI, hextI, ?_, hcond⟩
            exact (hinv.mono hextI hwf).insert
              (Nat.lt_of_lt_of_le hesz hextI.size_le)
              (cond_transport hextI hwf hesz hcond)
          · -- idx ≠ dd: unchanged
            rename_i hid
            cases hgo
            have hcond : ∀ x, st.denote e = some x →
                st.denote e = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.abstract1, hid] using hx
            exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstract1 dd k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstract1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun u hu => hwf.levels_lt e _ hn u (by simp [ENode.levels, hu]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstract1 dd k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstract1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstract1 dd k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstract1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstract1IGo dd st memo f k with ⟨f', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstract1IGo dd st₁ memo₁ a k with ⟨a', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.app f' a') with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih f hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih a hguard.2 hwf₁ hinv₁ h₂
            have hf₂ : st₂.denote f' = some (xf.abstract1 dd k) :=
              denote_mono hext₂ (hden₁ xf hf)
            have ha₂ : st₂.denote a' = some (xa.abstract1 dd k) :=
              hden₂ xa (denote_mono hext₁ ha)
            have hcI : ∀ c ∈ (ENode.app f' a').children, c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size hf₂
              · exact denote_lt_size ha₂
            have hwf₃ : (st₂.intern (.app f' a')).2.WF :=
              intern_wf hwf₂ hcI (by simp [ENode.levels]) (by simp [ENode.names])
            have hext₃ : Ext st₂ (st₂.intern (.app f' a')).2 := intern_ext _ _
            have hdI := intern_denote (n := .app f' a') hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hf₂, ha₂]
              simp [Expr.abstract1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstract1IGo dd st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstract1IGo dd st₁ memo₁ body (k + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.lam nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.abstract1 dd k) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.abstract1 dd (k + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.lam nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.lam nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.lam nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.lam nm ty' body' m)).2 := intern_ext _ _
            have hdI := intern_denote (n := .lam nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.abstract1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstract1IGo dd st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstract1IGo dd st₁ memo₁ body (k + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.forallE nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.abstract1 dd k) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.abstract1 dd (k + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.forallE nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.forallE nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.forallE nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.forallE nm ty' body' m)).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .forallE nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.abstract1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstract1IGo dd st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstract1IGo dd st₁ memo₁ val k with ⟨val', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : abstract1IGo dd st₂ memo₂ body (k + 1) with ⟨body', st₃, memo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.letE nm ty' val' body') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ :=
              ih val hguard.2.1 hwf₁ hinv₁ h₂
            obtain ⟨hwf₃, hext₃, hinv₃, hden₃⟩ :=
              ih body hguard.2.2 hwf₂ hinv₂ h₃
            have ht₃ : st₃.denote ty' = some (xt.abstract1 dd k) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hvv₃ : st₃.denote val' = some (xv.abstract1 dd k) :=
              denote_mono hext₃ (hden₂ xv (denote_mono hext₁ hvv))
            have hb₃ : st₃.denote body' = some (xb.abstract1 dd (k + 1)) :=
              hden₃ xb (denote_mono hext₂ (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.letE nm ty' val' body').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hvv₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.letE nm ty' val' body')).2.WF :=
              intern_wf hwf₃ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.letE nm ty' val' body')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .letE nm ty' val' body') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hvv₃, hb₃,
                denoteN_mono (hext₁.trans (hext₂.trans hext₃)) hnm]
              simp [Expr.abstract1]
            refine ⟨hwf₄, hextAll, ?_, hcond⟩
            exact (hinv₃.mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : abstract1IGo dd st memo sub k with ⟨sub', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.intern (.proj s j sub') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih sub hguard hwf hinv h₁
            have hs₁ : st₁.denote sub' = some (xs.abstract1 dd k) := hden₁ xs hs
            have hcI : ∀ c ∈ (ENode.proj s j sub').children,
                c < st₁.nodes.size := by
              simpa [ENode.children] using denote_lt_size hs₁
            have hwf₂ : (st₁.intern (.proj s j sub')).2.WF := intern_wf hwf₁ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  hext₁.nsize_le)
            have hext₂ : Ext st₁ (st₁.intern (.proj s j sub')).2 := intern_ext _ _
            have hdI := intern_denote (n := .proj s j sub') hwf₁ hcI
            rw [h₂] at hwf₂ hext₂ hdI
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denote e = some x →
                st₂.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hs₁, denoteN_mono hext₁ hnm]
              simp [Expr.abstract1]
            refine ⟨hwf₂, hextAll, ?_, hcond⟩
            exact (hinv₁.mono hext₂ hwf₁).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)

/-! ## `abstractRangeI` commutes with `denote` (task #72) -/

theorem abstractRangeIGo_spec {dd kk : Nat} :
    ∀ (e : EIdx) {st : EStore} {memo : MemoN} {k : Nat} {r : EIdx}
      {st' : EStore} {memo' : MemoN},
      st.WF →
      MemoNInv st (fun x c => x.abstractRange dd kk c) memo →
      abstractRangeIGo dd kk st memo e k = (r, st', memo') →
      st'.WF ∧ Ext st st' ∧
        MemoNInv st' (fun x c => x.abstractRange dd kk c) memo' ∧
        ∀ x, st.denote e = some x → st'.denote r = some (x.abstractRange dd kk k) := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro st memo k r st' memo' hwf hinv hgo
    unfold abstractRangeIGo at hgo
    split at hgo
    · -- per-node fvar-range cutoff: no fvar at or above the range base
      rename_i hcut
      cases hgo
      refine ⟨hwf, Ext.refl st, hinv, ?_⟩
      intro x hx
      rw [abstractRange_eq_self (hwf.fvarRangeD_le hx hcut)]
      exact hx
    split at hgo
    · rename_i hhit
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, (hinv _ _ _ hhit).2⟩
    · split at hgo
      · rename_i hnone
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstractRange dd kk k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstractRange] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          obtain ⟨xt, hxt⟩ := denote_total hwf t
            (Nat.lt_trans (hcl t (by simp [ENode.children])) hesz)
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.fvar idx nmv xt) := by
            rw [hde, denoteNode, hxt, hnm]; rfl
          split at hgo
          · -- dd ≤ idx < dd + kk: abstracted to the range's bvar
            rename_i hid
            rcases hI : st.intern (.bvar (k + (dd + kk - 1 - idx)))
              with ⟨ri, sti⟩
            rw [hI] at hgo
            cases hgo
            have hwfI : (st.intern (.bvar (k + (dd + kk - 1 - idx)))).2.WF :=
              intern_wf hwf (by simp [ENode.children]) (by simp [ENode.levels]) (by simp [ENode.names])
            have hextI : Ext st (st.intern (.bvar (k + (dd + kk - 1 - idx)))).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .bvar (k + (dd + kk - 1 - idx)))
              hwf (by simp [ENode.children])
            rw [hI] at hwfI hextI hdI
            have hcond : ∀ x, st.denote e = some x →
                sti.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI]
              simp [Expr.abstractRange, denoteNode, hid]
            refine ⟨hwfI, hextI, ?_, hcond⟩
            exact (hinv.mono hextI hwf).insert
              (Nat.lt_of_lt_of_le hesz hextI.size_le)
              (cond_transport hextI hwf hesz hcond)
          · -- outside the range: unchanged
            rename_i hid
            cases hgo
            have hcond : ∀ x, st.denote e = some x →
                st.denote e = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.abstractRange, hid] using hx
            exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstractRange dd kk k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstractRange] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun u hu => hwf.levels_lt e _ hn u (by simp [ENode.levels, hu]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstractRange dd kk k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstractRange] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstractRange dd kk k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstractRange] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstractRangeIGo dd kk st memo f k with ⟨f', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstractRangeIGo dd kk st₁ memo₁ a k with ⟨a', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.app f' a') with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih f hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih a hguard.2 hwf₁ hinv₁ h₂
            have hf₂ : st₂.denote f' = some (xf.abstractRange dd kk k) :=
              denote_mono hext₂ (hden₁ xf hf)
            have ha₂ : st₂.denote a' = some (xa.abstractRange dd kk k) :=
              hden₂ xa (denote_mono hext₁ ha)
            have hcI : ∀ c ∈ (ENode.app f' a').children, c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size hf₂
              · exact denote_lt_size ha₂
            have hwf₃ : (st₂.intern (.app f' a')).2.WF :=
              intern_wf hwf₂ hcI (by simp [ENode.levels]) (by simp [ENode.names])
            have hext₃ : Ext st₂ (st₂.intern (.app f' a')).2 := intern_ext _ _
            have hdI := intern_denote (n := .app f' a') hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hf₂, ha₂]
              simp [Expr.abstractRange]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstractRangeIGo dd kk st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstractRangeIGo dd kk st₁ memo₁ body (k + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.lam nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.abstractRange dd kk k) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.abstractRange dd kk (k + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.lam nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.lam nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.lam nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.lam nm ty' body' m)).2 := intern_ext _ _
            have hdI := intern_denote (n := .lam nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.abstractRange]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstractRangeIGo dd kk st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstractRangeIGo dd kk st₁ memo₁ body (k + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.forallE nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.abstractRange dd kk k) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.abstractRange dd kk (k + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.forallE nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.forallE nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.forallE nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.forallE nm ty' body' m)).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .forallE nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.abstractRange]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstractRangeIGo dd kk st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstractRangeIGo dd kk st₁ memo₁ val k with ⟨val', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : abstractRangeIGo dd kk st₂ memo₂ body (k + 1) with ⟨body', st₃, memo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.letE nm ty' val' body') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ :=
              ih val hguard.2.1 hwf₁ hinv₁ h₂
            obtain ⟨hwf₃, hext₃, hinv₃, hden₃⟩ :=
              ih body hguard.2.2 hwf₂ hinv₂ h₃
            have ht₃ : st₃.denote ty' = some (xt.abstractRange dd kk k) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hvv₃ : st₃.denote val' = some (xv.abstractRange dd kk k) :=
              denote_mono hext₃ (hden₂ xv (denote_mono hext₁ hvv))
            have hb₃ : st₃.denote body' = some (xb.abstractRange dd kk (k + 1)) :=
              hden₃ xb (denote_mono hext₂ (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.letE nm ty' val' body').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hvv₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.letE nm ty' val' body')).2.WF :=
              intern_wf hwf₃ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.letE nm ty' val' body')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .letE nm ty' val' body') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hvv₃, hb₃,
                denoteN_mono (hext₁.trans (hext₂.trans hext₃)) hnm]
              simp [Expr.abstractRange]
            refine ⟨hwf₄, hextAll, ?_, hcond⟩
            exact (hinv₃.mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : abstractRangeIGo dd kk st memo sub k with ⟨sub', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.intern (.proj s j sub') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih sub hguard hwf hinv h₁
            have hs₁ : st₁.denote sub' = some (xs.abstractRange dd kk k) := hden₁ xs hs
            have hcI : ∀ c ∈ (ENode.proj s j sub').children,
                c < st₁.nodes.size := by
              simpa [ENode.children] using denote_lt_size hs₁
            have hwf₂ : (st₁.intern (.proj s j sub')).2.WF := intern_wf hwf₁ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  hext₁.nsize_le)
            have hext₂ : Ext st₁ (st₁.intern (.proj s j sub')).2 := intern_ext _ _
            have hdI := intern_denote (n := .proj s j sub') hwf₁ hcI
            rw [h₂] at hwf₂ hext₂ hdI
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denote e = some x →
                st₂.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hs₁, denoteN_mono hext₁ hnm]
              simp [Expr.abstractRange]
            refine ⟨hwf₂, hextAll, ?_, hcond⟩
            exact (hinv₁.mono hext₂ hwf₁).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)

/-- `abstractRangeI` commutes with `denote`.  The `k = 0` shortcut is
covered by `abstractRange_zero`. -/
theorem abstractRangeI_spec {st : EStore} {e : EIdx} {d k c : Nat} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    (st.abstractRangeI e d k c).2.WF ∧
      Ext st (st.abstractRangeI e d k c).2 ∧
      (st.abstractRangeI e d k c).2.denote (st.abstractRangeI e d k c).1
        = some (a.abstractRange d k c) := by
  match k with
  | 0 =>
    refine ⟨hwf, Ext.refl st, ?_⟩
    rw [abstractRange_zero]
    exact he
  | k + 1 =>
    rcases hgo : abstractRangeIGo d (k + 1) st {} e c with ⟨r, st', memo'⟩
    obtain ⟨hwf', hext', -, hcond⟩ :=
      abstractRangeIGo_spec e hwf MemoNInv.empty hgo
    simp only [abstractRangeI, hgo]
    exact ⟨hwf', hext', hcond a he⟩

/-- `abstract1I` commutes with `denote`. -/
theorem abstract1I_spec {st : EStore} {e : EIdx} {d k : Nat} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    (st.abstract1I e d k).2.WF ∧ Ext st (st.abstract1I e d k).2 ∧
      (st.abstract1I e d k).2.denote (st.abstract1I e d k).1
        = some (a.abstract1 d k) := by
  rcases hgo : abstract1IGo d st {} e k with ⟨r, st', memo'⟩
  obtain ⟨hwf', hext', -, hcond⟩ := abstract1IGo_spec e hwf MemoNInv.empty hgo
  simp only [abstract1I, hgo]
  exact ⟨hwf', hext', hcond a he⟩

/-! ## `instantiateLevelParamsI` commutes with `denote` -/

/-- Cursor-free variant of `MemoNInv` for the level-substitution
traversal. -/
def Memo0Inv (st : EStore) (g : Expr → Expr) (memo : Memo0) : Prop :=
  ∀ (e r : EIdx), memo[e]? = some r →
    e < st.nodes.size ∧ ∀ x, st.denote e = some x → st.denote r = some (g x)

theorem Memo0Inv.empty {st : EStore} {g : Expr → Expr} : Memo0Inv st g {} := by
  intro e r hr
  simp at hr

theorem Memo0Inv.mono {st st' : EStore} {g : Expr → Expr} {memo : Memo0}
    (hext : Ext st st') (hwf : st.WF) (h : Memo0Inv st g memo) : Memo0Inv st' g memo := by
  intro e r hr
  obtain ⟨hlt, hcond⟩ := h e r hr
  refine ⟨Nat.lt_of_lt_of_le hlt hext.size_le, ?_⟩
  intro x hx
  rw [hext.denote_eq_of_lt hwf hlt] at hx
  exact denote_mono hext (hcond x hx)

theorem Memo0Inv.insert {st : EStore} {g : Expr → Expr} {memo : Memo0}
    {e r : EIdx} (h : Memo0Inv st g memo) (hlt : e < st.nodes.size)
    (hcond : ∀ x, st.denote e = some x → st.denote r = some (g x)) :
    Memo0Inv st g (memo.insert e r) := by
  intro e' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : e = e'
  · subst hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact ⟨hlt, hcond⟩
  · rw [if_neg (by simpa using hk)] at hr'
    exact h e' r' hr'

/-! ### The level-substitution layer (task #62) -/

/-- Invariant of a level index→index memo implementing the level
function `g`. -/
def LvlMemoInv (st : EStore) (g : Level → Level) (memo : LMemo) : Prop :=
  ∀ (u r : LIdx), memo[u]? = some r →
    u < st.lnodes.size ∧ ∀ x, st.denoteL u = some x → st.denoteL r = some (g x)

theorem LvlMemoInv.empty {st : EStore} {g : Level → Level} :
    LvlMemoInv st g {} := by
  intro u r hr
  simp at hr

theorem LvlMemoInv.mono {st st' : EStore} {g : Level → Level} {memo : LMemo}
    (hext : Ext st st') (h : LvlMemoInv st g memo) : LvlMemoInv st' g memo := by
  intro u r hr
  obtain ⟨hlt, hcond⟩ := h u r hr
  refine ⟨Nat.lt_of_lt_of_le hlt hext.lsize_le, ?_⟩
  intro x hx
  rw [hext.denoteL_eq_of_lt hlt] at hx
  exact denoteL_mono hext (hcond x hx)

theorem LvlMemoInv.insert {st : EStore} {g : Level → Level} {memo : LMemo}
    {u r : LIdx} (h : LvlMemoInv st g memo) (hlt : u < st.lnodes.size)
    (hcond : ∀ x, st.denoteL u = some x → st.denoteL r = some (g x)) :
    LvlMemoInv st g (memo.insert u r) := by
  intro u' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : u = u'
  · subst hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact ⟨hlt, hcond⟩
  · rw [if_neg (by simpa using hk)] at hr'
    exact h u' r' hr'

/-- Level-side `cond_transport`. -/
theorem condL_transport {st st' : EStore} (hext : Ext st st') {u r : LIdx}
    (husz : u < st.lnodes.size) {g : Level → Level}
    (hcond : ∀ x, st.denoteL u = some x → st'.denoteL r = some (g x)) :
    ∀ x, st'.denoteL u = some x → st'.denoteL r = some (g x) := by
  intro x hx
  rw [hext.denoteL_eq_of_lt husz] at hx
  exact hcond x hx

/-- `substLGo?` agrees with `Level.subst.go` under the denotation. -/
theorem substLGo?_spec {st : EStore} :
    ∀ {ks : List Name} {us : List LIdx} {lus : List Level} (n : Name),
      denoteLList st.denoteL us = some lus →
      (∀ v, substLGo? ks us n = some v →
        st.denoteL v = some (Level.subst.go ks lus n)) ∧
      (substLGo? ks us n = none → Level.subst.go ks lus n = .param n) := by
  intro ks
  induction ks with
  | nil =>
    intro us lus n hus
    cases us with
    | nil =>
      cases lus with
      | nil => exact ⟨by simp [substLGo?], fun _ => by simp [Level.subst.go]⟩
      | cons l ls => simp [denoteLList] at hus
    | cons u us' =>
      simp only [denoteLList, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hus
      obtain ⟨l, hl, ls, hls, rfl⟩ := hus
      exact ⟨by simp [substLGo?], fun _ => by simp [Level.subst.go]⟩
  | cons k ks ih =>
    intro us lus n hus
    cases us with
    | nil =>
      cases lus with
      | nil => exact ⟨by simp [substLGo?], fun _ => by simp [Level.subst.go]⟩
      | cons l ls => simp [denoteLList] at hus
    | cons u us' =>
      simp only [denoteLList, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hus
      obtain ⟨l, hl, ls, hls, rfl⟩ := hus
      by_cases hkn : k = n
      · subst hkn
        refine ⟨fun v hv => ?_, fun hnone => ?_⟩
        · simp only [substLGo?] at hv
          cases hv
          simpa [Level.subst.go] using hl
        · simp [substLGo?] at hnone
      · refine ⟨fun v hv => ?_, fun hnone => ?_⟩
        · simp only [substLGo?, if_neg hkn] at hv
          simpa [Level.subst.go, hkn] using (ih n hls).1 v hv
        · simp only [substLGo?, if_neg hkn] at hnone
          simpa [Level.subst.go, hkn] using (ih n hls).2 hnone

/-- `substLIGo` commutes with the denotation (the level analog of
`instantiate1IGo_spec`). -/
theorem substLIGo_spec {ks : List Name} {us : List LIdx} {lus : List Level} :
    ∀ (u : LIdx) {st : EStore} {memo : LMemo} {r : LIdx}
      {st' : EStore} {memo' : LMemo},
      st.WF → denoteLList st.denoteL us = some lus →
      LvlMemoInv st (Level.subst ks lus) memo →
      substLIGo ks us st memo u = (r, st', memo') →
      st'.WF ∧ Ext st st' ∧
        LvlMemoInv st' (Level.subst ks lus) memo' ∧
        ∀ x, st.denoteL u = some x → st'.denoteL r = some (Level.subst ks lus x) := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro st memo r st' memo' hwf hus hinv hgo
    unfold substLIGo at hgo
    split at hgo
    · -- param-free: identity (task #87)
      rename_i hnp
      cases hgo
      refine ⟨hwf, Ext.refl st, hinv, ?_⟩
      intro x hx
      rw [Level.subst_eq_self (hwf.lhasParamD_false hx hnp)]
      exact hx
    split at hgo
    · rename_i hhit
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, (hinv _ _ hhit).2⟩
    · split at hgo
      · rename_i hnone
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denoteL_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have husz : u < st.lnodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.lchildren_lt u n hn
        have hde := denoteL_node hn hcl
        cases n with
        | zero =>
          dsimp only at hgo
          cases hgo
          have hx : st.denoteL u = some .zero := by rw [hde]; rfl
          have hcond : ∀ x, st.denoteL u = some x →
              st.denoteL u = some (Level.subst ks lus x) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Level.subst] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert husz hcond, hcond⟩
        | param p =>
          dsimp only at hgo
          have hx : st.denoteL u = some (.param p) := by rw [hde]; rfl
          split at hgo
          · rename_i v hv
            cases hgo
            have hcond : ∀ x, st.denoteL u = some x →
                st.denoteL v = some (Level.subst ks lus x) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Level.subst] using (substLGo?_spec p hus).1 v hv
            exact ⟨hwf, Ext.refl st, hinv.insert husz hcond, hcond⟩
          · rename_i hvnone
            cases hgo
            have hcond : ∀ x, st.denoteL u = some x →
                st.denoteL u = some (Level.subst ks lus x) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hx, Level.subst, (substLGo?_spec p hus).2 hvnone]
            exact ⟨hwf, Ext.refl st, hinv.insert husz hcond, hcond⟩
        | succ l =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl l (by simp [LNode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : substLIGo ks us st memo l with ⟨l', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.internL (.succ l') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xl, hl⟩ := denoteL_total hwf l (Nat.lt_trans hguard husz)
            have hx : st.denoteL u = some (.succ xl) := by
              rw [hde, denoteLNode, hl]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih l hguard hwf hus hinv h₁
            have hl₁ : st₁.denoteL l' = some (Level.subst ks lus xl) :=
              hden₁ xl hl
            have hstep := internL_step (n := .succ l') hwf₁
              (by simpa [LNode.children] using denoteL_lt_size hl₁)
              (a := .succ (Level.subst ks lus xl))
              (by rw [denoteLNode, hl₁]; rfl)
            rw [h₂] at hstep
            obtain ⟨hwf₂, hext₂, hden₂⟩ := hstep
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denoteL u = some x →
                st₂.denoteL ri = some (Level.subst ks lus x) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Level.subst] using hden₂
            refine ⟨hwf₂, hextAll, ?_, hcond⟩
            exact ((hinv₁.mono hext₂).insert
              (Nat.lt_of_lt_of_le husz hextAll.lsize_le)
              (condL_transport hextAll husz hcond))
        | max l r' =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl l (by simp [LNode.children]),
              hcl r' (by simp [LNode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : substLIGo ks us st memo l with ⟨l', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : substLIGo ks us st₁ memo₁ r' with ⟨r₂, st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.internL (.max l' r₂) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xl, hl⟩ := denoteL_total hwf l (Nat.lt_trans hguard.1 husz)
            obtain ⟨xr, hr⟩ := denoteL_total hwf r' (Nat.lt_trans hguard.2 husz)
            have hx : st.denoteL u = some (.max xl xr) := by
              rw [hde, denoteLNode, hl, hr]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih l hguard.1 hwf hus hinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih r' hguard.2 hwf₁ hus₁ hinv₁ h₂
            have hl₂ : st₂.denoteL l' = some (Level.subst ks lus xl) :=
              denoteL_mono hext₂ (hden₁ xl hl)
            have hr₂ : st₂.denoteL r₂ = some (Level.subst ks lus xr) :=
              hden₂ xr (denoteL_mono hext₁ hr)
            have hstep := internL_step (n := .max l' r₂) hwf₂
              (by
                simp only [LNode.children, List.mem_cons, List.not_mem_nil,
                  or_false]
                rintro c (rfl | rfl)
                · exact denoteL_lt_size hl₂
                · exact denoteL_lt_size hr₂)
              (a := .max (Level.subst ks lus xl) (Level.subst ks lus xr))
              (by rw [denoteLNode, hl₂, hr₂]; rfl)
            rw [h₃] at hstep
            obtain ⟨hwf₃, hext₃, hden₃⟩ := hstep
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denoteL u = some x →
                st₃.denoteL ri = some (Level.subst ks lus x) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Level.subst] using hden₃
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact ((hinv₂.mono hext₃).insert
              (Nat.lt_of_lt_of_le husz hextAll.lsize_le)
              (condL_transport hextAll husz hcond))
        | imax l r' =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl l (by simp [LNode.children]),
              hcl r' (by simp [LNode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : substLIGo ks us st memo l with ⟨l', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : substLIGo ks us st₁ memo₁ r' with ⟨r₂, st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.internL (.imax l' r₂) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xl, hl⟩ := denoteL_total hwf l (Nat.lt_trans hguard.1 husz)
            obtain ⟨xr, hr⟩ := denoteL_total hwf r' (Nat.lt_trans hguard.2 husz)
            have hx : st.denoteL u = some (.imax xl xr) := by
              rw [hde, denoteLNode, hl, hr]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih l hguard.1 hwf hus hinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih r' hguard.2 hwf₁ hus₁ hinv₁ h₂
            have hl₂ : st₂.denoteL l' = some (Level.subst ks lus xl) :=
              denoteL_mono hext₂ (hden₁ xl hl)
            have hr₂ : st₂.denoteL r₂ = some (Level.subst ks lus xr) :=
              hden₂ xr (denoteL_mono hext₁ hr)
            have hstep := internL_step (n := .imax l' r₂) hwf₂
              (by
                simp only [LNode.children, List.mem_cons, List.not_mem_nil,
                  or_false]
                rintro c (rfl | rfl)
                · exact denoteL_lt_size hl₂
                · exact denoteL_lt_size hr₂)
              (a := .imax (Level.subst ks lus xl) (Level.subst ks lus xr))
              (by rw [denoteLNode, hl₂, hr₂]; rfl)
            rw [h₃] at hstep
            obtain ⟨hwf₃, hext₃, hden₃⟩ := hstep
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denoteL u = some x →
                st₃.denoteL ri = some (Level.subst ks lus x) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Level.subst] using hden₃
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact ((hinv₂.mono hext₃).insert
              (Nat.lt_of_lt_of_le husz hextAll.lsize_le)
              (condL_transport hextAll husz hcond))

/-- `substLIList` commutes with the denotation. -/
theorem substLIList_spec {ks : List Name} {us : List LIdx} {lus : List Level} :
    ∀ (vs : List LIdx) {st : EStore} {memo : LMemo} {rs : List LIdx}
      {st' : EStore} {memo' : LMemo},
      st.WF → denoteLList st.denoteL us = some lus →
      LvlMemoInv st (Level.subst ks lus) memo →
      substLIList ks us st memo vs = (rs, st', memo') →
      st'.WF ∧ Ext st st' ∧
        LvlMemoInv st' (Level.subst ks lus) memo' ∧
        ∀ xs, denoteLList st.denoteL vs = some xs →
          denoteLList st'.denoteL rs = some (xs.map (Level.subst ks lus)) := by
  intro vs
  induction vs with
  | nil =>
    intro st memo rs st' memo' hwf hus hinv hgo
    cases hgo
    refine ⟨hwf, Ext.refl st, hinv, ?_⟩
    intro xs hxs
    cases hxs
    rfl
  | cons v vs ih =>
    intro st memo rs st' memo' hwf hus hinv hgo
    dsimp only [substLIList] at hgo
    rcases h₁ : substLIGo ks us st memo v with ⟨v', st₁, memo₁⟩
    rw [h₁] at hgo
    rcases h₂ : substLIList ks us st₁ memo₁ vs with ⟨vs', st₂, memo₂⟩
    rw [h₂] at hgo
    cases hgo
    obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := substLIGo_spec v hwf hus hinv h₁
    have hus₁ := denoteLList_mono hext₁ hus
    obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih hwf₁ hus₁ hinv₁ h₂
    refine ⟨hwf₂, hext₁.trans hext₂, hinv₂, ?_⟩
    intro xs hxs
    simp only [denoteLList, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hxs
    obtain ⟨l, hl, ls, hls, rfl⟩ := hxs
    have hv' : st₂.denoteL v' = some (Level.subst ks lus l) :=
      denoteL_mono hext₂ (hden₁ l hl)
    have hvs' := hden₂ ls (denoteLList_mono hext₁ hls)
    simp [denoteLList, hv', hvs']

/-- `substLIBM` commutes with the denotation. -/
theorem substLIBM_spec {ks : List Name} {us : List LIdx} {lus : List Level}
    {m : IBinderMeta} {st : EStore} {memo : LMemo} {m' : IBinderMeta}
    {st' : EStore} {memo' : LMemo}
    (hwf : st.WF) (hus : denoteLList st.denoteL us = some lus)
    (hinv : LvlMemoInv st (Level.subst ks lus) memo)
    (hgo : substLIBM ks us st memo m = (m', st', memo')) :
    st'.WF ∧ Ext st st' ∧
      LvlMemoInv st' (Level.subst ks lus) memo' ∧
      ∀ bm, denoteBM st.denoteL m = some bm →
        denoteBM st'.denoteL m'
          = some ⟨bm.bi, bm.cod.map (Level.subst ks lus)⟩ := by
  obtain ⟨bi, (_ | u)⟩ := m
  · cases hgo
    refine ⟨hwf, Ext.refl st, hinv, ?_⟩
    intro bm hbm
    simp only [denoteBM, Option.some.injEq] at hbm
    subst hbm
    rfl
  · dsimp only [substLIBM] at hgo
    rcases h₁ : substLIGo ks us st memo u with ⟨u', st₁, memo₁⟩
    rw [h₁] at hgo
    cases hgo
    obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := substLIGo_spec u hwf hus hinv h₁
    refine ⟨hwf₁, hext₁, hinv₁, ?_⟩
    intro bm hbm
    simp only [denoteBM, Option.map_eq_some_iff] at hbm
    obtain ⟨l, hl, rfl⟩ := hbm
    simp [denoteBM, hden₁ l hl]

theorem instantiateLevelParamsIGo_spec {ks : List Name} {us : List LIdx}
    {lus : List Level} :
    ∀ (e : EIdx) {st : EStore} {memo : Memo0} {lmemo : LMemo} {r : EIdx}
      {st' : EStore} {memo' : Memo0} {lmemo' : LMemo},
      st.WF →
      denoteLList st.denoteL us = some lus →
      Memo0Inv st (Expr.instantiateLevelParams ks lus) memo →
      LvlMemoInv st (Level.subst ks lus) lmemo →
      instantiateLevelParamsIGo ks us st memo lmemo e = (r, st', memo', lmemo') →
      st'.WF ∧ Ext st st' ∧
        Memo0Inv st' (Expr.instantiateLevelParams ks lus) memo' ∧
        LvlMemoInv st' (Level.subst ks lus) lmemo' ∧
        ∀ x, st.denote e = some x →
          st'.denote r = some (x.instantiateLevelParams ks lus) := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro st memo lmemo r st' memo' lmemo' hwf hus hinv hlinv hgo
    unfold instantiateLevelParamsIGo at hgo
    split at hgo
    · -- level-param-free: identity (task #87)
      rename_i hnp
      cases hgo
      refine ⟨hwf, Ext.refl st, hinv, hlinv, ?_⟩
      intro x hx
      rw [Expr.instantiateLevelParams_eq_self (hwf.ehasParamD_false hx hnp)]
      exact hx
    split at hgo
    · rename_i hhit
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, hlinv, (hinv _ _ hhit).2⟩
    · split at hgo
      · rename_i hnone
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, hlinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiateLevelParams ks lus) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiateLevelParams] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hlinv, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl t (by simp [ENode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo t
              with ⟨t', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.intern (.fvar idx nm t') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xt, hxt⟩ := denote_total hwf t (Nat.lt_trans hguard hesz)
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hwf.names_lt e _ hn nm (by simp [ENode.names]))
            have hx : st.denote e = some (.fvar idx nmv xt) := by
              rw [hde, denoteNode, hxt, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih t hguard hwf hus hinv hlinv h₁
            have ht₁ : st₁.denote t' = some (xt.instantiateLevelParams ks lus) :=
              hden₁ xt hxt
            have hcI : ∀ c ∈ (ENode.fvar idx nm t').children,
                c < st₁.nodes.size := by
              simpa [ENode.children] using denote_lt_size ht₁
            have hwf₂ : (st₁.intern (.fvar idx nm t')).2.WF :=
              intern_wf hwf₁ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  hext₁.nsize_le)
            have hext₂ : Ext st₁ (st₁.intern (.fvar idx nm t')).2 := intern_ext _ _
            have hdI := intern_denote (n := .fvar idx nm t') hwf₁ hcI
            rw [h₂] at hwf₂ hext₂ hdI
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denote e = some x →
                st₂.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₁, denoteN_mono hext₁ hnm]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₂, hextAll, ?_, hlinv₁.mono hext₂, hcond⟩
            exact (hinv₁.mono hext₂ hwf₁).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | sort u =>
          dsimp only at hgo
          rcases h₁ : substLIGo ks us st lmemo u with ⟨u', st₁, lmemo₁⟩
          rw [h₁] at hgo
          rcases h₂ : st₁.intern (.sort u') with ⟨ri, st₂⟩
          rw [h₂] at hgo
          cases hgo
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          obtain ⟨hwf₁, hext₁, hlinv₁, hlden₁⟩ := substLIGo_spec u hwf hus hlinv h₁
          have hu₁ : st₁.denoteL u' = some (Level.subst ks lus lu) :=
            hlden₁ lu hlu
          have hwf₂ : (st₁.intern (.sort u')).2.WF :=
            intern_wf hwf₁ (by simp [ENode.children])
              (by simpa [ENode.levels] using denoteL_lt_size hu₁)
              (by simp [ENode.names])
          have hext₂ : Ext st₁ (st₁.intern (.sort u')).2 := intern_ext _ _
          have hdI := intern_denote (n := .sort u') hwf₁
            (by simp [ENode.children])
          rw [h₂] at hwf₂ hext₂ hdI
          have hextAll : Ext st st₂ := hext₁.trans hext₂
          have hcond : ∀ x, st.denote e = some x →
              st₂.denote ri = some (x.instantiateLevelParams ks lus) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            rw [hdI, denoteNode, hu₁]
            simp [Expr.instantiateLevelParams]
          refine ⟨hwf₂, hextAll, ?_, hlinv₁.mono hext₂, hcond⟩
          exact (hinv.mono hextAll hwf).insert
            (Nat.lt_of_lt_of_le hesz hextAll.size_le)
            (cond_transport hextAll hwf hesz hcond)
        | const nm vs =>
          dsimp only at hgo
          rcases h₁ : substLIList ks us st lmemo vs with ⟨vs', st₁, lmemo₁⟩
          rw [h₁] at hgo
          rcases h₂ : st₁.intern (.const nm vs') with ⟨ri, st₂⟩
          rw [h₂] at hgo
          cases hgo
          obtain ⟨lvs, hlvs⟩ := denoteLList_total hwf vs
            (fun u hu => hwf.levels_lt e _ hn u (by simp [ENode.levels, hu]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lvs) := by
            rw [hde, denoteNode, hlvs, hnm]; rfl
          obtain ⟨hwf₁, hext₁, hlinv₁, hlden₁⟩ :=
            substLIList_spec vs hwf hus hlinv h₁
          have hvs₁ : denoteLList st₁.denoteL vs'
              = some (lvs.map (Level.subst ks lus)) := hlden₁ lvs hlvs
          have hwf₂ : (st₁.intern (.const nm vs')).2.WF :=
            intern_wf hwf₁ (by simp [ENode.children])
              (by simpa [ENode.levels] using denoteLList_lt_size hvs₁)
              (fun p hp => Nat.lt_of_lt_of_le
                (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                hext₁.nsize_le)
          have hext₂ : Ext st₁ (st₁.intern (.const nm vs')).2 := intern_ext _ _
          have hdI := intern_denote (n := .const nm vs') hwf₁
            (by simp [ENode.children])
          rw [h₂] at hwf₂ hext₂ hdI
          have hextAll : Ext st st₂ := hext₁.trans hext₂
          have hcond : ∀ x, st.denote e = some x →
              st₂.denote ri = some (x.instantiateLevelParams ks lus) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            rw [hdI, denoteNode, hvs₁, denoteN_mono hext₁ hnm]
            simp [Expr.instantiateLevelParams]
          refine ⟨hwf₂, hextAll, ?_, hlinv₁.mono hext₂, hcond⟩
          exact (hinv.mono hextAll hwf).insert
            (Nat.lt_of_lt_of_le hesz hextAll.size_le)
            (cond_transport hextAll hwf hesz hcond)
        | lit l =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiateLevelParams ks lus) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiateLevelParams] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hlinv, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo f
              with ⟨f', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiateLevelParamsIGo ks us st₁ memo₁ lmemo₁ a
              with ⟨a', st₂, memo₂, lmemo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.app f' a') with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih f hguard.1 hwf hus hinv hlinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hlinv₂, hden₂⟩ :=
              ih a hguard.2 hwf₁ hus₁ hinv₁ hlinv₁ h₂
            have hf₂ : st₂.denote f' = some (xf.instantiateLevelParams ks lus) :=
              denote_mono hext₂ (hden₁ xf hf)
            have ha₂ : st₂.denote a' = some (xa.instantiateLevelParams ks lus) :=
              hden₂ xa (denote_mono hext₁ ha)
            have hcI : ∀ c ∈ (ENode.app f' a').children, c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size hf₂
              · exact denote_lt_size ha₂
            have hwf₃ : (st₂.intern (.app f' a')).2.WF :=
              intern_wf hwf₂ hcI (by simp [ENode.levels])
                (by simp [ENode.names])
            have hext₃ : Ext st₂ (st₂.intern (.app f' a')).2 := intern_ext _ _
            have hdI := intern_denote (n := .app f' a') hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hf₂, ha₂]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₃, hextAll, ?_, hlinv₂.mono hext₃, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo ty
              with ⟨ty', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiateLevelParamsIGo ks us st₁ memo₁ lmemo₁ body
              with ⟨body', st₂, memo₂, lmemo₂⟩
            rw [h₂] at hgo
            rcases h₃ : substLIBM ks us st₂ lmemo₂ m with ⟨m', st₃, lmemo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.lam nm ty' body' m') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih ty hguard.1 hwf hus hinv hlinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hlinv₂, hden₂⟩ :=
              ih body hguard.2 hwf₁ hus₁ hinv₁ hlinv₁ h₂
            have hus₂ := denoteLList_mono hext₂ hus₁
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            obtain ⟨hwf₃, hext₃, hlinv₃, hbden₃⟩ :=
              substLIBM_spec hwf₂ hus₂ hlinv₂ h₃
            have hm₃ : denoteBM st₃.denoteL m'
                = some ⟨bm.bi, bm.cod.map (Level.subst ks lus)⟩ := hbden₃ bm hbm₂
            have ht₃ : st₃.denote ty' = some (xt.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hb₃ : st₃.denote body'
                = some (xb.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (hden₂ xb (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.lam nm ty' body' m').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.lam nm ty' body' m')).2.WF :=
              intern_wf hwf₃ hcI
                (by simpa [ENode.levels] using denoteBM_lt_size hm₃)
                (fun p hp => Nat.lt_of_lt_of_le
                  (hnms p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.lam nm ty' body' m')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .lam nm ty' body' m') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hb₃, hm₃,
                denoteN_mono hext₃ hnm₂]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₄, hextAll, ?_, hlinv₃.mono hext₄, hcond⟩
            exact ((hinv₂.mono hext₃ hwf₂).mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo ty
              with ⟨ty', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiateLevelParamsIGo ks us st₁ memo₁ lmemo₁ body
              with ⟨body', st₂, memo₂, lmemo₂⟩
            rw [h₂] at hgo
            rcases h₃ : substLIBM ks us st₂ lmemo₂ m with ⟨m', st₃, lmemo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.forallE nm ty' body' m') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih ty hguard.1 hwf hus hinv hlinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hlinv₂, hden₂⟩ :=
              ih body hguard.2 hwf₁ hus₁ hinv₁ hlinv₁ h₂
            have hus₂ := denoteLList_mono hext₂ hus₁
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            obtain ⟨hwf₃, hext₃, hlinv₃, hbden₃⟩ :=
              substLIBM_spec hwf₂ hus₂ hlinv₂ h₃
            have hm₃ : denoteBM st₃.denoteL m'
                = some ⟨bm.bi, bm.cod.map (Level.subst ks lus)⟩ := hbden₃ bm hbm₂
            have ht₃ : st₃.denote ty' = some (xt.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hb₃ : st₃.denote body'
                = some (xb.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (hden₂ xb (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.forallE nm ty' body' m').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.forallE nm ty' body' m')).2.WF :=
              intern_wf hwf₃ hcI
                (by simpa [ENode.levels] using denoteBM_lt_size hm₃)
                (fun p hp => Nat.lt_of_lt_of_le
                  (hnms p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.forallE nm ty' body' m')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .forallE nm ty' body' m') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hb₃, hm₃,
                denoteN_mono hext₃ hnm₂]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₄, hextAll, ?_, hlinv₃.mono hext₄, hcond⟩
            exact ((hinv₂.mono hext₃ hwf₂).mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo ty
              with ⟨ty', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiateLevelParamsIGo ks us st₁ memo₁ lmemo₁ val
              with ⟨val', st₂, memo₂, lmemo₂⟩
            rw [h₂] at hgo
            rcases h₃ : instantiateLevelParamsIGo ks us st₂ memo₂ lmemo₂ body
              with ⟨body', st₃, memo₃, lmemo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.letE nm ty' val' body') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih ty hguard.1 hwf hus hinv hlinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hlinv₂, hden₂⟩ :=
              ih val hguard.2.1 hwf₁ hus₁ hinv₁ hlinv₁ h₂
            have hus₂ := denoteLList_mono hext₂ hus₁
            obtain ⟨hwf₃, hext₃, hinv₃, hlinv₃, hden₃⟩ :=
              ih body hguard.2.2 hwf₂ hus₂ hinv₂ hlinv₂ h₃
            have ht₃ : st₃.denote ty' = some (xt.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hvv₃ : st₃.denote val'
                = some (xv.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (hden₂ xv (denote_mono hext₁ hvv))
            have hb₃ : st₃.denote body'
                = some (xb.instantiateLevelParams ks lus) :=
              hden₃ xb (denote_mono hext₂ (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.letE nm ty' val' body').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hvv₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.letE nm ty' val' body')).2.WF :=
              intern_wf hwf₃ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.letE nm ty' val' body')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .letE nm ty' val' body') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hvv₃, hb₃,
                denoteN_mono (hext₁.trans (hext₂.trans hext₃)) hnm]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₄, hextAll, ?_, hlinv₃.mono hext₄, hcond⟩
            exact (hinv₃.mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo sub
              with ⟨sub', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.intern (.proj s j sub') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih sub hguard hwf hus hinv hlinv h₁
            have hs₁ : st₁.denote sub' = some (xs.instantiateLevelParams ks lus) :=
              hden₁ xs hs
            have hcI : ∀ c ∈ (ENode.proj s j sub').children,
                c < st₁.nodes.size := by
              simpa [ENode.children] using denote_lt_size hs₁
            have hwf₂ : (st₁.intern (.proj s j sub')).2.WF :=
              intern_wf hwf₁ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  hext₁.nsize_le)
            have hext₂ : Ext st₁ (st₁.intern (.proj s j sub')).2 := intern_ext _ _
            have hdI := intern_denote (n := .proj s j sub') hwf₁ hcI
            rw [h₂] at hwf₂ hext₂ hdI
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denote e = some x →
                st₂.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hs₁, denoteN_mono hext₁ hnm]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₂, hextAll, ?_, hlinv₁.mono hext₂, hcond⟩
            exact (hinv₁.mono hext₂ hwf₁).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)

/-- `instantiateLevelParamsI` commutes with `denote` (the replacement
levels are interned indices, their denotations the substituted
levels). -/
theorem instantiateLevelParamsI_spec {st : EStore} {ks : List Name}
    {us : List LIdx} {lus : List Level} {e : EIdx} {a : Expr}
    (hwf : st.WF) (hus : denoteLList st.denoteL us = some lus)
    (he : st.denote e = some a) :
    (st.instantiateLevelParamsI ks us e).2.WF ∧
      Ext st (st.instantiateLevelParamsI ks us e).2 ∧
      (st.instantiateLevelParamsI ks us e).2.denote
          (st.instantiateLevelParamsI ks us e).1
        = some (a.instantiateLevelParams ks lus) := by
  rcases hgo : instantiateLevelParamsIGo ks us st {} {} e
    with ⟨r, st', memo', lmemo'⟩
  obtain ⟨hwf', hext', -, -, hcond⟩ :=
    instantiateLevelParamsIGo_spec e hwf hus Memo0Inv.empty LvlMemoInv.empty hgo
  simp only [instantiateLevelParamsI, hgo]
  exact ⟨hwf', hext', hcond a he⟩


/-! ## Pure queries agree with the `Expr` versions

The queries never change the store, so their memo invariants need
neither the range component nor extension transport. -/

/-- Memo invariant for a cursor-free query implementing `g`. -/
def QMemo0Inv {β : Type} (st : EStore) (g : Expr → β)
    (memo : Std.HashMap EIdx β) : Prop :=
  ∀ (e : EIdx) (r : β), memo[e]? = some r →
    ∀ x, st.denote e = some x → r = g x

theorem QMemo0Inv.empty {β : Type} {st : EStore} {g : Expr → β} :
    QMemo0Inv st g {} := by
  intro e r hr
  simp at hr

theorem QMemo0Inv.insert {β : Type} {st : EStore} {g : Expr → β}
    {memo : Std.HashMap EIdx β} {e : EIdx} {r : β}
    (h : QMemo0Inv st g memo)
    (hcond : ∀ x, st.denote e = some x → r = g x) :
    QMemo0Inv st g (memo.insert e r) := by
  intro e' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : e = e'
  · subst hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact hcond
  · rw [if_neg (by simpa using hk)] at hr'
    exact h e' r' hr'

/-- Memo invariant for a query with a `Nat` cursor implementing `g`. -/
def QMemoNInv {β : Type} (st : EStore) (g : Expr → Nat → β)
    (memo : Std.HashMap (EIdx × Nat) β) : Prop :=
  ∀ (e : EIdx) (c : Nat) (r : β), memo[(e, c)]? = some r →
    ∀ x, st.denote e = some x → r = g x c

theorem QMemoNInv.empty {β : Type} {st : EStore} {g : Expr → Nat → β} :
    QMemoNInv st g {} := by
  intro e c r hr
  simp at hr

theorem QMemoNInv.insert {β : Type} {st : EStore} {g : Expr → Nat → β}
    {memo : Std.HashMap (EIdx × Nat) β} {e : EIdx} {c : Nat} {r : β}
    (h : QMemoNInv st g memo)
    (hcond : ∀ x, st.denote e = some x → r = g x c) :
    QMemoNInv st g (memo.insert (e, c) r) := by
  intro e' c' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : (e, c) = (e', c')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact hcond
  · rw [if_neg (by simpa using hk)] at hr'
    exact h e' c' r' hr'

/-- `hasFvarI` agrees with `Expr.hasFvar` — an `O(1)` consequence of
the eager range entry's exactness (task #87). -/
theorem hasFvarI_spec {st : EStore} {e : EIdx} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    st.hasFvarI e = a.hasFvar := by
  show (st.fvarRangeD e != 0) = a.hasFvar
  rw [hwf.fvarRangeD_exact e he, fvarRange_bne_zero]


theorem looseBVarsBoundedIGo_spec {st : EStore} (hwf : st.WF) :
    ∀ (e : EIdx) {memo : Std.HashMap (EIdx × Nat) Bool} {k : Nat} {r : Bool}
      {memo' : Std.HashMap (EIdx × Nat) Bool},
      QMemoNInv st (fun x c => x.looseBVarsBounded c) memo →
      looseBVarsBoundedIGo st memo k e = (r, memo') →
      QMemoNInv st (fun x c => x.looseBVarsBounded c) memo' ∧
        ∀ x, st.denote e = some x → r = x.looseBVarsBounded k := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro memo k r memo' hinv hgo
    unfold looseBVarsBoundedIGo at hgo
    split at hgo
    · rename_i hhit
      injection hgo with hgr hgm
      subst hgr
      subst hgm
      exact ⟨hinv, hinv _ _ _ hhit⟩
    · split at hgo
      · rename_i hnone
        injection hgo with hgr hgm
        subst hgr
        subst hgm
        refine ⟨hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              decide (i < k) = x.looseBVarsBounded k := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.looseBVarsBounded]
          exact ⟨hinv.insert hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨xt, hxt⟩ := denote_total hwf t
            (Nat.lt_trans (hcl t (by simp [ENode.children])) hesz)
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.fvar idx nmv xt) := by
            rw [hde, denoteNode, hxt, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              true = x.looseBVarsBounded k := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.looseBVarsBounded]
          exact ⟨hinv.insert hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x →
              true = x.looseBVarsBounded k := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.looseBVarsBounded]
          exact ⟨hinv.insert hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun v hv => hwf.levels_lt e _ hn v (by simp [ENode.levels, hv]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              true = x.looseBVarsBounded k := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.looseBVarsBounded]
          exact ⟨hinv.insert hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              true = x.looseBVarsBounded k := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.looseBVarsBounded]
          exact ⟨hinv.insert hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            rcases h₁ : looseBVarsBoundedIGo st memo k f with ⟨rf, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih f hguard.1 hinv h₁
            split at hgo
            · -- rf = true: continue with the argument
              rename_i hrf
              rcases h₂ : looseBVarsBoundedIGo st memo₁ k a with ⟨ra, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih a hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  ra = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [hrf] at h1
                simp [Expr.looseBVarsBounded, ← h1, ← hden₂ xa ha]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · -- rf = false: short-circuit false
              rename_i hrf
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [Bool.not_eq_true] at hrf
                rw [hrf] at h1
                simp [Expr.looseBVarsBounded, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : looseBVarsBoundedIGo st memo k ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : looseBVarsBoundedIGo st memo₁ (k + 1) body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  rb = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.looseBVarsBounded, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.looseBVarsBounded, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : looseBVarsBoundedIGo st memo k ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : looseBVarsBoundedIGo st memo₁ (k + 1) body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  rb = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.looseBVarsBounded, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.looseBVarsBounded, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            rcases h₁ : looseBVarsBoundedIGo st memo k ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : looseBVarsBoundedIGo st memo₁ k val with ⟨rv, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              obtain ⟨hinv₂, hden₂⟩ := ih val hguard.2.1 hinv₁ h₂
              split at hgo
              · rename_i hrv
                rcases h₃ : looseBVarsBoundedIGo st memo₂ (k + 1) body with ⟨rb, memo₃⟩
                rw [h₃] at hgo
                try dsimp only at hgo
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                obtain ⟨hinv₃, hden₃⟩ := ih body hguard.2.2 hinv₂ h₃
                have hcond : ∀ x, st.denote e = some x →
                    rb = x.looseBVarsBounded k := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h1 := hden₁ xt ht
                  have h2 := hden₂ xv hvv
                  rw [hrt] at h1
                  rw [hrv] at h2
                  simp [Expr.looseBVarsBounded, ← h1, ← h2, ← hden₃ xb hb]
                exact ⟨hinv₃.insert hcond, hcond⟩
              · rename_i hrv
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                have hcond : ∀ x, st.denote e = some x →
                    false = x.looseBVarsBounded k := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h2 := hden₂ xv hvv
                  rw [Bool.not_eq_true] at hrv
                  rw [hrv] at h2
                  simp [Expr.looseBVarsBounded, ← h2]
                exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.looseBVarsBounded, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            rcases h₁ : looseBVarsBoundedIGo st memo k sub with ⟨rs, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih sub hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x →
                rs = x.looseBVarsBounded k := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.looseBVarsBounded] using hden₁ xs hs
            exact ⟨hinv₁.insert hcond, hcond⟩

/-- `looseBVarsBoundedI` agrees with `Expr.looseBVarsBounded`. -/
theorem looseBVarsBoundedI_spec {st : EStore} {k : Nat} {e : EIdx} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    st.looseBVarsBoundedI k e = a.looseBVarsBounded k := by
  rcases hgo : looseBVarsBoundedIGo st {} k e with ⟨r, memo'⟩
  obtain ⟨-, hcond⟩ := looseBVarsBoundedIGo_spec hwf e QMemoNInv.empty hgo
  simp only [looseBVarsBoundedI, hgo]
  exact hcond a he

theorem wscopedBIGo_spec {st : EStore} (hwf : st.WF) :
    ∀ (e : EIdx) {memo : Std.HashMap (EIdx × Nat) Bool} {d : Nat} {r : Bool}
      {memo' : Std.HashMap (EIdx × Nat) Bool},
      QMemoNInv st (fun x c => x.wscopedB c) memo →
      wscopedBIGo st memo d e = (r, memo') →
      QMemoNInv st (fun x c => x.wscopedB c) memo' ∧
        ∀ x, st.denote e = some x → r = x.wscopedB d := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro memo d r memo' hinv hgo
    unfold wscopedBIGo at hgo
    split at hgo
    · rename_i hhit
      injection hgo with hgr hgm
      subst hgr
      subst hgm
      exact ⟨hinv, hinv _ _ _ hhit⟩
    · split at hgo
      · rename_i hnone
        injection hgo with hgr hgm
        subst hgr
        subst hgm
        refine ⟨hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.wscopedB d := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.wscopedB]
          exact ⟨hinv.insert hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.wscopedB d := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.wscopedB]
          exact ⟨hinv.insert hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun v hv => hwf.levels_lt e _ hn v (by simp [ENode.levels, hv]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.wscopedB d := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.wscopedB]
          exact ⟨hinv.insert hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.wscopedB d := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.wscopedB]
          exact ⟨hinv.insert hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl t (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xt, hxt⟩ := denote_total hwf t (Nat.lt_trans hguard hesz)
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hwf.names_lt e _ hn nm (by simp [ENode.names]))
            have hx : st.denote e = some (.fvar idx nmv xt) := by
              rw [hde, denoteNode, hxt, hnm]; rfl
            split at hgo
            · -- idx < d: recurse into the annotation at cutoff idx
              rename_i hlt
              rcases h₁ : wscopedBIGo st memo idx t with ⟨rt, memo₁⟩
              rw [h₁] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₁, hden₁⟩ := ih t hguard hinv h₁
              have hcond : ∀ x, st.denote e = some x → rt = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp [Expr.wscopedB, hlt, ← hden₁ xt hxt]
              exact ⟨hinv₁.insert hcond, hcond⟩
            · rename_i hlt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp [Expr.wscopedB, hlt]
              exact ⟨hinv.insert hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            rcases h₁ : wscopedBIGo st memo d f with ⟨rf, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih f hguard.1 hinv h₁
            split at hgo
            · rename_i hrf
              rcases h₂ : wscopedBIGo st memo₁ d a with ⟨ra, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih a hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x → ra = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [hrf] at h1
                simp [Expr.wscopedB, ← h1, ← hden₂ xa ha]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrf
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [Bool.not_eq_true] at hrf
                rw [hrf] at h1
                simp [Expr.wscopedB, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : wscopedBIGo st memo d ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : wscopedBIGo st memo₁ d body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x → rb = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.wscopedB, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.wscopedB, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : wscopedBIGo st memo d ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : wscopedBIGo st memo₁ d body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x → rb = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.wscopedB, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.wscopedB, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            rcases h₁ : wscopedBIGo st memo d ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : wscopedBIGo st memo₁ d val with ⟨rv, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              obtain ⟨hinv₂, hden₂⟩ := ih val hguard.2.1 hinv₁ h₂
              split at hgo
              · rename_i hrv
                rcases h₃ : wscopedBIGo st memo₂ d body with ⟨rb, memo₃⟩
                rw [h₃] at hgo
                try dsimp only at hgo
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                obtain ⟨hinv₃, hden₃⟩ := ih body hguard.2.2 hinv₂ h₃
                have hcond : ∀ x, st.denote e = some x → rb = x.wscopedB d := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h1 := hden₁ xt ht
                  have h2 := hden₂ xv hvv
                  rw [hrt] at h1
                  rw [hrv] at h2
                  simp [Expr.wscopedB, ← h1, ← h2, ← hden₃ xb hb]
                exact ⟨hinv₃.insert hcond, hcond⟩
              · rename_i hrv
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h2 := hden₂ xv hvv
                  rw [Bool.not_eq_true] at hrv
                  rw [hrv] at h2
                  simp [Expr.wscopedB, ← h2]
                exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.wscopedB, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            rcases h₁ : wscopedBIGo st memo d sub with ⟨rs, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih sub hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x → rs = x.wscopedB d := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.wscopedB] using hden₁ xs hs
            exact ⟨hinv₁.insert hcond, hcond⟩

/-- `wscopedBI` agrees with `Expr.wscopedB`. -/
theorem wscopedBI_spec {st : EStore} {d : Nat} {e : EIdx} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    st.wscopedBI d e = a.wscopedB d := by
  rcases hgo : wscopedBIGo st {} d e with ⟨r, memo'⟩
  obtain ⟨-, hcond⟩ := wscopedBIGo_spec hwf e QMemoNInv.empty hgo
  simp only [wscopedBI, hgo]
  exact hcond a he

theorem constsResolveIGo_spec {st : EStore} {env : Env} (hwf : st.WF) :
    ∀ (e : EIdx) {memo : Std.HashMap EIdx Bool} {r : Bool}
      {memo' : Std.HashMap EIdx Bool},
      QMemo0Inv st (fun x => x.constsResolve env) memo →
      constsResolveIGo st env memo e = (r, memo') →
      QMemo0Inv st (fun x => x.constsResolve env) memo' ∧
        ∀ x, st.denote e = some x → r = x.constsResolve env := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro memo r memo' hinv hgo
    unfold constsResolveIGo at hgo
    split at hgo
    · rename_i hhit
      injection hgo with hgr hgm
      subst hgr
      subst hgm
      exact ⟨hinv, hinv _ _ hhit⟩
    · split at hgo
      · rename_i hnone
        injection hgo with hgr hgm
        subst hgr
        subst hgm
        refine ⟨hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.constsResolve env := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.constsResolve]
          exact ⟨hinv.insert hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.constsResolve env := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.constsResolve]
          exact ⟨hinv.insert hcond, hcond⟩
        | lit l =>
          cases l with
          | strVal sv =>
            dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            have hx : st.denote e = some (.lit (.strVal sv)) := by
              rw [hde]; rfl
            have hcond : ∀ x, st.denote e = some x →
                ((env.find? natName).isSome && (env.find? natZeroName).isSome &&
                  (env.find? natSuccName).isSome &&
                  (env.find? stringName).isSome &&
                  (env.find? stringOfListName).isSome &&
                  (env.find? listName).isSome &&
                  (env.find? listNilName).isSome &&
                  (env.find? listConsName).isSome &&
                  (env.find? charName).isSome &&
                  (env.find? charOfNatName).isSome) = x.constsResolve env := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simp [Expr.constsResolve]
            exact ⟨hinv.insert hcond, hcond⟩
          | natVal nv =>
            dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            have hx : st.denote e = some (.lit (.natVal nv)) := by
              rw [hde]; rfl
            have hcond : ∀ x, st.denote e = some x →
                ((env.find? natName).isSome &&
                  (env.find? natZeroName).isSome &&
                  (env.find? natSuccName).isSome) = x.constsResolve env := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simp [Expr.constsResolve]
            exact ⟨hinv.insert hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun v hv => hwf.levels_lt e _ hn v (by simp [ENode.levels, hv]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              (match st.readbackN nm with
               | some name => (env.find? name).isSome
               | none => false) = x.constsResolve env := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            rw [hwf.readbackN_eq_denoteN, hnm]
            simp [Expr.constsResolve]
          exact ⟨hinv.insert hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl t (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xt, hxt⟩ := denote_total hwf t (Nat.lt_trans hguard hesz)
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hwf.names_lt e _ hn nm (by simp [ENode.names]))
            have hx : st.denote e = some (.fvar idx nmv xt) := by
              rw [hde, denoteNode, hxt, hnm]; rfl
            rcases h₁ : constsResolveIGo st env memo t with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih t hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x → rt = x.constsResolve env := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.constsResolve] using hden₁ xt hxt
            exact ⟨hinv₁.insert hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            rcases h₁ : constsResolveIGo st env memo f with ⟨rf, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih f hguard.1 hinv h₁
            split at hgo
            · rename_i hrf
              rcases h₂ : constsResolveIGo st env memo₁ a with ⟨ra, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih a hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  ra = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [hrf] at h1
                simp [Expr.constsResolve, ← h1, ← hden₂ xa ha]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrf
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [Bool.not_eq_true] at hrf
                rw [hrf] at h1
                simp [Expr.constsResolve, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : constsResolveIGo st env memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : constsResolveIGo st env memo₁ body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  rb = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.constsResolve, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.constsResolve, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : constsResolveIGo st env memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : constsResolveIGo st env memo₁ body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  rb = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.constsResolve, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.constsResolve, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            rcases h₁ : constsResolveIGo st env memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : constsResolveIGo st env memo₁ val with ⟨rv, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              obtain ⟨hinv₂, hden₂⟩ := ih val hguard.2.1 hinv₁ h₂
              split at hgo
              · rename_i hrv
                rcases h₃ : constsResolveIGo st env memo₂ body with ⟨rb, memo₃⟩
                rw [h₃] at hgo
                try dsimp only at hgo
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                obtain ⟨hinv₃, hden₃⟩ := ih body hguard.2.2 hinv₂ h₃
                have hcond : ∀ x, st.denote e = some x →
                    rb = x.constsResolve env := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h1 := hden₁ xt ht
                  have h2 := hden₂ xv hvv
                  rw [hrt] at h1
                  rw [hrv] at h2
                  simp [Expr.constsResolve, ← h1, ← h2, ← hden₃ xb hb]
                exact ⟨hinv₃.insert hcond, hcond⟩
              · rename_i hrv
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                have hcond : ∀ x, st.denote e = some x →
                    false = x.constsResolve env := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h2 := hden₂ xv hvv
                  rw [Bool.not_eq_true] at hrv
                  rw [hrv] at h2
                  simp [Expr.constsResolve, ← h2]
                exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.constsResolve, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            rw [hwf.readbackN_eq_denoteN, hnm] at hgo
            dsimp only at hgo
            split at hgo
            · -- struct name resolves: recurse
              rename_i hres
              rcases h₁ : constsResolveIGo st env memo sub with ⟨rs, memo₁⟩
              rw [h₁] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₁, hden₁⟩ := ih sub hguard hinv h₁
              have hcond : ∀ x, st.denote e = some x →
                  rs = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp [Expr.constsResolve, hres, ← hden₁ xs hs]
              exact ⟨hinv₁.insert hcond, hcond⟩
            · rename_i hres
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [Bool.not_eq_true] at hres
                simp [Expr.constsResolve, hres]
              exact ⟨hinv.insert hcond, hcond⟩

/-- `constsResolveI` agrees with `Expr.constsResolve`. -/
theorem constsResolveI_spec {st : EStore} {env : Env} {e : EIdx} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    st.constsResolveI env e = a.constsResolve env := by
  rcases hgo : constsResolveIGo st env {} e with ⟨r, memo'⟩
  obtain ⟨-, hcond⟩ := constsResolveIGo_spec hwf e QMemo0Inv.empty hgo
  simp only [constsResolveI, hgo]
  exact hcond a he

/-! ### `fvarLeavesI`

The interned leaf list carries type *indices*; it agrees with
`Expr.fvarLeaves` after mapping the denotation over the type
component. -/

/-- Denotation image of an interned leaf list (name components
through the name denotation, task #88). -/
def leavesDen (st : EStore) (r : List (Nat × NIdx × EIdx)) :
    List (Nat × Option Name × Option Expr) :=
  r.map fun l => (l.1, st.denoteN l.2.1, st.denote l.2.2)

/-- The `Expr`-side leaf list in the same shape. -/
def leavesExp (x : Expr) : List (Nat × Option Name × Option Expr) :=
  x.fvarLeaves.map fun l => (l.1, some l.2.1, some l.2.2)

theorem leavesDen_append {st : EStore} {r₁ r₂ : List (Nat × NIdx × EIdx)} :
    leavesDen st (r₁ ++ r₂) = leavesDen st r₁ ++ leavesDen st r₂ :=
  List.map_append ..

/-- Memo invariant for the leaf-list traversal. -/
def LMemoInv (st : EStore)
    (memo : Std.HashMap EIdx (List (Nat × NIdx × EIdx))) : Prop :=
  ∀ (e : EIdx) (r : List (Nat × NIdx × EIdx)), memo[e]? = some r →
    ∀ x, st.denote e = some x → leavesDen st r = leavesExp x

theorem LMemoInv.empty {st : EStore} : LMemoInv st {} := by
  intro e r hr
  simp at hr

theorem LMemoInv.insert {st : EStore}
    {memo : Std.HashMap EIdx (List (Nat × NIdx × EIdx))} {e : EIdx}
    {r : List (Nat × NIdx × EIdx)} (h : LMemoInv st memo)
    (hcond : ∀ x, st.denote e = some x → leavesDen st r = leavesExp x) :
    LMemoInv st (memo.insert e r) := by
  intro e' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : e = e'
  · subst hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact hcond
  · rw [if_neg (by simpa using hk)] at hr'
    exact h e' r' hr'

theorem fvarLeavesIGo_spec {st : EStore} (hwf : st.WF) :
    ∀ (e : EIdx) {memo : Std.HashMap EIdx (List (Nat × NIdx × EIdx))}
      {r : List (Nat × NIdx × EIdx)}
      {memo' : Std.HashMap EIdx (List (Nat × NIdx × EIdx))},
      LMemoInv st memo →
      fvarLeavesIGo st memo e = (r, memo') →
      LMemoInv st memo' ∧
        ∀ x, st.denote e = some x → leavesDen st r = leavesExp x := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro memo r memo' hinv hgo
    unfold fvarLeavesIGo at hgo
    split at hgo
    · rename_i hhit
      injection hgo with hgr hgm
      subst hgr
      subst hgm
      exact ⟨hinv, hinv _ _ hhit⟩
    · split at hgo
      · rename_i hnone
        injection hgo with hgr hgm
        subst hgr
        subst hgm
        refine ⟨hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              leavesDen st [] = leavesExp x := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [leavesDen, leavesExp, Expr.fvarLeaves]
          exact ⟨hinv.insert hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x →
              leavesDen st [] = leavesExp x := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [leavesDen, leavesExp, Expr.fvarLeaves]
          exact ⟨hinv.insert hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun v hv => hwf.levels_lt e _ hn v (by simp [ENode.levels, hv]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              leavesDen st [] = leavesExp x := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [leavesDen, leavesExp, Expr.fvarLeaves]
          exact ⟨hinv.insert hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              leavesDen st [] = leavesExp x := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [leavesDen, leavesExp, Expr.fvarLeaves]
          exact ⟨hinv.insert hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl t (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xt, hxt⟩ := denote_total hwf t (Nat.lt_trans hguard hesz)
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hwf.names_lt e _ hn nm (by simp [ENode.names]))
            have hx : st.denote e = some (.fvar idx nmv xt) := by
              rw [hde, denoteNode, hxt, hnm]; rfl
            rcases h₁ : fvarLeavesIGo st memo t with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih t hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st ((idx, nm, t) :: rt) = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              have := hden₁ xt hxt
              simp only [leavesDen, leavesExp, List.map_cons, Expr.fvarLeaves] at *
              simp [hxt, this, hnm]
            exact ⟨hinv₁.insert hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            rcases h₁ : fvarLeavesIGo st memo f with ⟨rf, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            rcases h₂ : fvarLeavesIGo st memo₁ a with ⟨ra, memo₂⟩
            rw [h₂] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih f hguard.1 hinv h₁
            obtain ⟨hinv₂, hden₂⟩ := ih a hguard.2 hinv₁ h₂
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st (rf ++ ra) = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [leavesDen_append, hden₁ xf hf, hden₂ xa ha]
              simp [leavesExp, Expr.fvarLeaves]
            exact ⟨hinv₂.insert hcond, hcond⟩
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : fvarLeavesIGo st memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            rcases h₂ : fvarLeavesIGo st memo₁ body with ⟨rb, memo₂⟩
            rw [h₂] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st (rt ++ rb) = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [leavesDen_append, hden₁ xt ht, hden₂ xb hb]
              simp [leavesExp, Expr.fvarLeaves]
            exact ⟨hinv₂.insert hcond, hcond⟩
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : fvarLeavesIGo st memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            rcases h₂ : fvarLeavesIGo st memo₁ body with ⟨rb, memo₂⟩
            rw [h₂] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st (rt ++ rb) = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [leavesDen_append, hden₁ xt ht, hden₂ xb hb]
              simp [leavesExp, Expr.fvarLeaves]
            exact ⟨hinv₂.insert hcond, hcond⟩
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            rcases h₁ : fvarLeavesIGo st memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            rcases h₂ : fvarLeavesIGo st memo₁ val with ⟨rv, memo₂⟩
            rw [h₂] at hgo
            try dsimp only at hgo
            rcases h₃ : fvarLeavesIGo st memo₂ body with ⟨rb, memo₃⟩
            rw [h₃] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            obtain ⟨hinv₂, hden₂⟩ := ih val hguard.2.1 hinv₁ h₂
            obtain ⟨hinv₃, hden₃⟩ := ih body hguard.2.2 hinv₂ h₃
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st (rt ++ rv ++ rb) = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [leavesDen_append, leavesDen_append,
                hden₁ xt ht, hden₂ xv hvv, hden₃ xb hb]
              simp [leavesExp, Expr.fvarLeaves]
            exact ⟨hinv₃.insert hcond, hcond⟩
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            rcases h₁ : fvarLeavesIGo st memo sub with ⟨rs, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih sub hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st rs = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hden₁ xs hs]
              simp [leavesExp, Expr.fvarLeaves]
            exact ⟨hinv₁.insert hcond, hcond⟩

/-- `fvarLeavesI` agrees with `Expr.fvarLeaves` after denoting the type
components. -/
theorem fvarLeavesI_spec {st : EStore} {e : EIdx} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    leavesDen st (st.fvarLeavesI e) = leavesExp a := by
  rcases hgo : fvarLeavesIGo st {} e with ⟨r, memo'⟩
  obtain ⟨-, hcond⟩ := fvarLeavesIGo_spec hwf e LMemoInv.empty hgo
  simp only [fvarLeavesI, hgo]
  exact hcond a he


end EStore

end Setlec
