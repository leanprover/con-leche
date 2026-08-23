import Setlec.Verify.IExpr
import Setlec.Verify.InstList
import Setlec.Kernel.CoreI

/-!
# Specs for the interned core's arena operations (task #26)

Commutation of the spine/telescope/readback operations of
`Setlec/Kernel/IExpr.lean` with the structural denotation, the
`FEnv` name-index agreement with `Env.find?`, and the agreement of the
indexed guard twins (`Setlec/Kernel/CoreI.lean`) with their `Env`
originals.  Everything is stated over well-formed stores (`EStore.WF`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open EStore

/-! ## The pointwise list relation -/

/-- Pointwise denotation of an index list. -/
def DenL (st : EStore) : List EIdx → List Expr → Prop
  | [], [] => True
  | i :: is, x :: xs => st.denote i = some x ∧ DenL st is xs
  | _, _ => False

namespace DenL

theorem nil {st : EStore} : DenL st [] [] := trivial

theorem cons {st : EStore} {i : EIdx} {x : Expr} {is : List EIdx}
    {xs : List Expr} (h : st.denote i = some x) (hs : DenL st is xs) :
    DenL st (i :: is) (x :: xs) := ⟨h, hs⟩

theorem length_eq {st : EStore} :
    ∀ {is : List EIdx} {xs : List Expr}, DenL st is xs →
      is.length = xs.length
  | [], [], _ => rfl
  | _ :: is, _ :: xs, ⟨_, hs⟩ => by
    simpa using length_eq (is := is) (xs := xs) hs
  | [], _ :: _, h | _ :: _, [], h => nomatch h

theorem mono {st st' : EStore} (hext : Ext st st') :
    ∀ {is : List EIdx} {xs : List Expr}, DenL st is xs → DenL st' is xs
  | [], [], _ => trivial
  | _ :: is, _ :: xs, ⟨h, hs⟩ =>
    ⟨denote_mono hext h, mono hext (is := is) (xs := xs) hs⟩
  | [], _ :: _, h | _ :: _, [], h => nomatch h

theorem append {st : EStore} :
    ∀ {is is' : List EIdx} {xs xs' : List Expr}, DenL st is xs →
      DenL st is' xs' → DenL st (is ++ is') (xs ++ xs')
  | [], _, [], _, _, h' => h'
  | _ :: is, _, _ :: xs, _, ⟨h, hs⟩, h' =>
    ⟨h, append (is := is) (xs := xs) hs h'⟩
  | [], _, _ :: _, _, h, _ | _ :: _, _, [], _, h, _ => nomatch h

theorem take {st : EStore} (k : Nat) :
    ∀ {is : List EIdx} {xs : List Expr}, DenL st is xs →
      DenL st (is.take k) (xs.take k) := by
  induction k with
  | zero => intro is xs _; exact trivial
  | succ k ih =>
    intro is xs h
    match is, xs, h with
    | [], [], _ => exact trivial
    | i :: is, x :: xs, ⟨h, hs⟩ =>
      exact ⟨h, ih hs⟩

theorem drop {st : EStore} (k : Nat) :
    ∀ {is : List EIdx} {xs : List Expr}, DenL st is xs →
      DenL st (is.drop k) (xs.drop k) := by
  induction k with
  | zero => intro is xs h; exact h
  | succ k ih =>
    intro is xs h
    match is, xs, h with
    | [], [], _ => exact trivial
    | i :: is, x :: xs, ⟨_, hs⟩ =>
      exact ih hs

theorem getD {st : EStore} {d0 : EIdx} {x0 : Expr}
    (hd : st.denote d0 = some x0) :
    ∀ {is : List EIdx} {xs : List Expr} (k : Nat), DenL st is xs →
      st.denote (is.getD k d0) = some (xs.getD k x0)
  | [], [], _, _ => hd
  | i :: is, x :: xs, k, ⟨h, hs⟩ => by
    cases k with
    | zero => simpa using h
    | succ k =>
      simpa using getD hd (is := is) (xs := xs) k hs
  | [], _ :: _, _, h | _ :: _, [], _, h => nomatch h

theorem get {st : EStore} :
    ∀ {is : List EIdx} {xs : List Expr}, DenL st is xs →
      ∀ (k : Nat) (hk : k < is.length) (hk' : k < xs.length),
        st.denote is[k] = some xs[k]
  | i :: is, x :: xs, ⟨h, hs⟩, k, hk, hk' => by
    cases k with
    | zero => simpa using h
    | succ k =>
      simpa using get (is := is) (xs := xs) hs k (by simpa using hk)
        (by simpa using hk')
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => nomatch h

theorem reverse {st : EStore} :
    ∀ {is : List EIdx} {xs : List Expr}, DenL st is xs →
      DenL st is.reverse xs.reverse
  | [], [], _ => trivial
  | i :: is, x :: xs, ⟨h, hs⟩ => by
    rw [List.reverse_cons, List.reverse_cons]
    exact append (reverse (is := is) (xs := xs) hs) ⟨h, trivial⟩
  | [], _ :: _, h | _ :: _, [], h => nomatch h

end DenL

/-! ## Spine operations -/

theorem getAppFnI_spec {st : EStore} (_hwf : st.WF) :
    ∀ {e : EIdx} {x : Expr}, st.denote e = some x →
      st.denote (st.getAppFnI e) = some x.getAppFn := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro x hx
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hx
    cases n with
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨xf, hf, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨xa, ha, rfl⟩ := hd
      have hflt : f < e := hc f (by simp [ENode.children])
      rw [getAppFnI, hn]
      dsimp only
      rw [dif_pos hflt]
      rw [show Expr.getAppFn (.app xf xa) = xf.getAppFn from rfl]
      exact ih f hflt hf
    | bvar i =>
      cases hd; rw [getAppFnI, hn]; exact hx
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨lu, _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx
    | const nm us =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨lus, _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx
    | lit l => cases hd; rw [getAppFnI, hn]; exact hx
    | fvar idx nm t =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨t', _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx
    | lam nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨eb, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨bm, _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx
    | forallE nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨eb, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨bm, _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx
    | letE nm t v b =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨ev, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx
    | proj s j e' =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨ee, _, rfl⟩ := hd
      rw [getAppFnI, hn]; exact hx

theorem getAppArgsAccI_spec {st : EStore} (_hwf : st.WF) :
    ∀ {e : EIdx} {x : Expr}, st.denote e = some x →
      ∀ {acc : List EIdx} {xs : List Expr}, DenL st acc xs →
        DenL st (st.getAppArgsAccI e acc) (x.getAppArgs ++ xs) := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro x hx acc xs hacc
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hx
    cases n with
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨xf, hf, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨xa, ha, rfl⟩ := hd
      have hflt : f < e := hc f (by simp [ENode.children])
      rw [getAppArgsAccI, hn]
      dsimp only
      rw [dif_pos hflt]
      have := ih f hflt hf (acc := a :: acc) (xs := xa :: xs) ⟨ha, hacc⟩
      rw [show Expr.getAppArgs (.app xf xa) = xf.getAppArgs ++ [xa] from rfl,
        List.append_assoc]
      exact this
    | bvar i => cases hd; rw [getAppArgsAccI, hn]; exact hacc
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨lu, _, rfl⟩ := hd
      rw [getAppArgsAccI, hn]; exact hacc
    | const nm us =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨lus, _, rfl⟩ := hd
      rw [getAppArgsAccI, hn]; exact hacc
    | lit l => cases hd; rw [getAppArgsAccI, hn]; exact hacc
    | fvar idx nm t =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨t', _, rfl⟩ := hd
      rw [getAppArgsAccI, hn]; exact hacc
    | lam nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨eb, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨bm, _, rfl⟩ := hd
      rw [getAppArgsAccI, hn]; exact hacc
    | forallE nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨eb, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨bm, _, rfl⟩ := hd
      rw [getAppArgsAccI, hn]; exact hacc
    | letE nm t v b =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨ev, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [getAppArgsAccI, hn]; exact hacc
    | proj s j e' =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨ee, _, rfl⟩ := hd
      rw [getAppArgsAccI, hn]; exact hacc

theorem getAppArgsI_spec {st : EStore} (hwf : st.WF) :
    ∀ {e : EIdx} {x : Expr}, st.denote e = some x →
      DenL st (st.getAppArgsI e) x.getAppArgs := by
  intro e x hx
  have := getAppArgsAccI_spec hwf hx (acc := []) (xs := []) DenL.nil
  simpa [getAppArgsI] using this

/-- Elements of a denoted level-index list denote. -/
theorem denoteLList_some_mem {denL : LIdx → Option Level} :
    ∀ {us : List LIdx} {ls : List Level},
      denoteLList denL us = some ls → ∀ u ∈ us, ∃ l, denL u = some l := by
  intro us
  induction us with
  | nil => simp
  | cons u us ih =>
    intro ls h v hv
    simp only [denoteLList, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨l, hl, ls', hls', rfl⟩ := h
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact ⟨l, hl⟩
    · exact ih hls' v hv'

/-- `denoteBM` preserves the binder info. -/
theorem denoteBM_bi {denL : LIdx → Option Level} {m : IBinderMeta}
    {bm : BinderMeta} (h : denoteBM denL m = some bm) : bm.bi = m.bi := by
  obtain ⟨bi, (_ | u)⟩ := m
  · simp only [denoteBM, Option.some.injEq] at h
    subst h; rfl
  · simp only [denoteBM, Option.map_eq_some_iff] at h
    obtain ⟨l, -, rfl⟩ := h; rfl

/-- Level-index lists and their denotations have equal length. -/
theorem denoteLList_length {denL : LIdx → Option Level} :
    ∀ {us : List LIdx} {ls : List Level},
      denoteLList denL us = some ls → us.length = ls.length := by
  intro us
  induction us with
  | nil => intro ls h; cases h; rfl
  | cons u us ih =>
    intro ls h
    simp only [denoteLList, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨l, -, ls', hls', rfl⟩ := h
    simp [ih hls']

/-- `denoteBM` codomain inversion: `none` maps to `none`. -/
theorem denoteBM_none_iff {denL : LIdx → Option Level} {m : IBinderMeta}
    {bm : BinderMeta} (h : denoteBM denL m = some bm) :
    m.cod = none ↔ bm.cod = none := by
  obtain ⟨bi, (_ | u)⟩ := m
  · simp only [denoteBM, Option.some.injEq] at h
    subst h
    simp
  · simp only [denoteBM, Option.map_eq_some_iff] at h
    obtain ⟨l, -, rfl⟩ := h
    simp

/-- `denoteBM` codomain inversion: a `some` codomain denotes. -/
theorem denoteBM_some {denL : LIdx → Option Level} {m : IBinderMeta}
    {bm : BinderMeta} {u : LIdx} (h : denoteBM denL m = some bm)
    (hc : m.cod = some u) : ∃ l, denL u = some l ∧ bm.cod = some l := by
  obtain ⟨bi, (_ | v)⟩ := m
  · cases hc
  · cases hc
    simp only [denoteBM, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    exact ⟨l, hl, rfl⟩

/-- Level-index lists and their denotations are `nil` together. -/
theorem denoteLList_nil_iff {denL : LIdx → Option Level}
    {us : List LIdx} {ls : List Level}
    (h : denoteLList denL us = some ls) : us = [] ↔ ls = [] := by
  have := denoteLList_length h
  constructor
  · rintro rfl
    cases ls with
    | nil => rfl
    | cons l ls' => simp at this
  · rintro rfl
    cases us with
    | nil => rfl
    | cons u us' => simp at this

/-- `denoteLList` distributes over append. -/
theorem denoteLList_append {denL : LIdx → Option Level} :
    ∀ {us vs : List LIdx} {ls ms : List Level},
      denoteLList denL us = some ls → denoteLList denL vs = some ms →
      denoteLList denL (us ++ vs) = some (ls ++ ms) := by
  intro us
  induction us with
  | nil =>
    intro vs ls ms h1 h2
    cases h1
    simpa using h2
  | cons u us ih =>
    intro vs ls ms h1 h2
    simp only [denoteLList, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h1
    obtain ⟨l, hl, ls', hls', rfl⟩ := h1
    simp [denoteLList, hl, ih hls' h2]

/-- A denoted node's level references denote. -/
theorem denoteNode_levels_some {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {n : ENode} {a : Expr}
    (h : denoteNode den denL n = some a) :
    ∀ u ∈ n.levels, ∃ l, denL u = some l := by
  cases n with
  | sort u =>
    simp only [denoteNode, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    intro v hv
    simp only [ENode.levels, List.mem_singleton] at hv
    subst hv
    exact ⟨l, hl⟩
  | const nm us =>
    simp only [denoteNode, Option.map_eq_some_iff] at h
    obtain ⟨ls, hls, rfl⟩ := h
    simpa [ENode.levels] using denoteLList_some_mem hls
  | lam nm t b m =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨et, -, eb, -, bm, hbm, rfl⟩ := h
    intro u hu
    simp only [ENode.levels] at hu
    obtain ⟨bi, (_ | v)⟩ := m
    · simp at hu
    · simp only [Option.toList] at hu
      simp only [List.mem_singleton] at hu
      subst hu
      simp only [denoteBM, Option.map_eq_some_iff] at hbm
      obtain ⟨l, hl, -⟩ := hbm
      exact ⟨l, hl⟩
  | forallE nm t b m =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨et, -, eb, -, bm, hbm, rfl⟩ := h
    intro u hu
    simp only [ENode.levels] at hu
    obtain ⟨bi, (_ | v)⟩ := m
    · simp at hu
    · simp only [Option.toList] at hu
      simp only [List.mem_singleton] at hu
      subst hu
      simp only [denoteBM, Option.map_eq_some_iff] at hbm
      obtain ⟨l, hl, -⟩ := hbm
      exact ⟨l, hl⟩
  | bvar i => simp [ENode.levels]
  | lit l => simp [ENode.levels]
  | fvar idx nm t => simp [ENode.levels]
  | app f a' => simp [ENode.levels]
  | letE nm t v b => simp [ENode.levels]
  | proj sN j e' => simp [ENode.levels]

theorem intern_spec {st : EStore} {n : ENode} {a : Expr} (hwf : st.WF)
    (hd : denoteNode st.denote st.denoteL n = some a) :
    (st.intern n).2.WF ∧ Ext st (st.intern n).2 ∧
      (st.intern n).2.denote (st.intern n).1 = some a := by
  have hc : ∀ c ∈ n.children, c < st.nodes.size := by
    intro c hcin
    obtain ⟨b, hb⟩ := denoteNode_children_some hd c hcin
    exact denote_lt_size hb
  have hlv : ∀ u ∈ n.levels, u < st.lnodes.size := by
    intro u hu
    obtain ⟨l, hl⟩ := denoteNode_levels_some hd u hu
    exact denoteL_lt_size hl
  exact ⟨intern_wf hwf hc hlv, intern_ext st n,
    by rw [intern_denote hwf hc]; exact hd⟩

/-! ## Bulk instantiation commutes with `denote` (task #50) -/

/-- Invariant of the bulk-instantiation memo: every entry's key is in
range and maps denotation-consistently for the *prefix* of the
replacement denotations named by the key. -/
def MemoNLInv (st : EStore) (ws : List Expr) (memo : MemoNL) : Prop :=
  ∀ (e : EIdx) (k c : Nat) (r : EIdx), memo[(e, k, c)]? = some r →
    e < st.nodes.size ∧ ∀ x, st.denote e = some x →
      st.denote r = some (x.instantiateList (ws.take k) c)

theorem MemoNLInv.empty {st : EStore} {ws : List Expr} :
    MemoNLInv st ws {} := by
  intro e k c r hr
  simp at hr

theorem MemoNLInv.mono {st st' : EStore} {ws : List Expr}
    {memo : MemoNL} (hext : Ext st st') (hwf : st.WF)
    (h : MemoNLInv st ws memo) : MemoNLInv st' ws memo := by
  intro e k c r hr
  obtain ⟨hlt, hcond⟩ := h e k c r hr
  refine ⟨Nat.lt_of_lt_of_le hlt hext.size_le, ?_⟩
  intro x hx
  rw [hext.denote_eq_of_lt hwf hlt] at hx
  exact denote_mono hext (hcond x hx)

theorem MemoNLInv.insert {st : EStore} {ws : List Expr}
    {memo : MemoNL} {e : EIdx} {k c : Nat} {r : EIdx}
    (h : MemoNLInv st ws memo) (hlt : e < st.nodes.size)
    (hcond : ∀ x, st.denote e = some x →
      st.denote r = some (x.instantiateList (ws.take k) c)) :
    MemoNLInv st ws (memo.insert (e, k, c) r) := by
  intro e' k' c' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hkey : ((e, k, c) : EIdx × Nat × Nat) = (e', k', c')
  · obtain ⟨rfl, h2⟩ := Prod.mk.injEq .. ▸ hkey
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h2
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact ⟨hlt, hcond⟩
  · rw [if_neg (by simpa using hkey)] at hr'
    exact h e' k' c' r' hr'

/-- Correctness of the memoized bulk-instantiation core: on a
well-formed store, `instantiateListIGo` preserves the invariant,
extends the store, keeps the memo consistent, and its result denotes
`Expr.instantiateList` of the input's denotation at the live prefix of
the replacement denotations. -/
theorem instantiateListIGo_spec {vs : Array EIdx} {ws : List Expr}
    {bm0 : BMemo} :
    ∀ (k : Nat) (e : EIdx) {st : EStore} {memo : MemoNL} {d : Nat}
      {r : EIdx} {st' : EStore} {memo' : MemoNL},
      st.WF → DenL st vs.toList ws → k ≤ vs.size →
      EStore.BoundMemoInv st bm0 →
      MemoNLInv st ws memo →
      instantiateListIGo vs st bm0 memo e k d = (r, st', memo') →
      st'.WF ∧ Ext st st' ∧ MemoNLInv st' ws memo' ∧
        ∀ x, st.denote e = some x →
          st'.denote r = some (x.instantiateList (ws.take k) d) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro e
  induction e using Nat.strongRecOn with
  | _ e ihe =>
    intro st memo d r st' memo' hwf hvs hk hbm0 hinv hgo
    have hlen : ws.length = vs.size := by
      simpa using hvs.length_eq.symm
    unfold instantiateListIGo at hgo
    split at hgo
    · -- k = 0: the identity (empty live prefix)
      rename_i hk0
      cases hgo
      subst hk0
      refine ⟨hwf, Ext.refl st, hinv, ?_⟩
      intro x hx
      simpa [Expr.instantiateList_nil] using hx
    · rename_i hk0
      split at hgo
      · -- per-node bound cutoff (task #84)
        rename_i hcut
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        intro x hx
        obtain ⟨b, hget, hble⟩ := EStore.BMemo.cutoff_eq_true hcut
        rw [Expr.instantiateList_eq_self
          (EStore.lbbMono hble ((hbm0 e b hget).2 x hx))]
        exact hx
      rename_i hncut
      have htklen : (ws.take k).length = k := by
        simp [List.length_take]
        omega
      split at hgo
      · -- memo hit
        rename_i hhit
        cases hgo
        exact ⟨hwf, Ext.refl st, hinv, (hinv _ _ _ _ hhit).2⟩
      · split at hgo
        · -- index out of range: identity, but no denotation exists
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
            · -- i < d: untouched
              rename_i hid
              cases hgo
              have hcond : ∀ x, st.denote e = some x →
                  st.denote e = some (x.instantiateList (ws.take k) d) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp [Expr.instantiateList, hid, hx]
              exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
            · rename_i hid
              split at hgo
              · -- i - d < k: the replacement, recursively substituted
                rename_i hidk
                split at hgo
                · rename_i hidv
                  rcases hrec : instantiateListIGo vs st bm0 memo vs[i - d]
                      (i - d) d with ⟨r₁, st₁, memo₁⟩
                  rw [hrec] at hgo
                  cases hgo
                  obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ :=
                    ihk (i - d) hidk vs[i - d] hwf hvs
                      (Nat.le_of_lt hidv) hbm0 hinv hrec
                  have hwlt : i - d < ws.length := by omega
                  have hvd : st.denote vs[i - d] = some ws[i - d] := by
                    have := hvs.get (i - d) (by simpa using hidv)
                      (by simpa using hwlt)
                    simpa using this
                  have hcond : ∀ x, st.denote e = some x →
                      st₁.denote r₁
                        = some (x.instantiateList (ws.take k) d) := by
                    intro x hxx
                    rw [hx] at hxx; cases hxx
                    have hgoal : (Expr.bvar i).instantiateList (ws.take k) d
                        = ws[i - d].instantiateList (ws.take (i - d)) d := by
                      rw [Expr.instantiateList, if_neg hid,
                        dif_pos (by omega : i - d < (ws.take k).length)]
                      congr 1
                      · exact List.getElem_take
                      · rw [List.take_take]
                        congr 1
                        omega
                    rw [hgoal]
                    exact hden₁ ws[i - d] hvd
                  refine ⟨hwf₁, hext₁, ?_, hcond⟩
                  exact hinv₁.insert
                    (Nat.lt_of_lt_of_le hesz hext₁.size_le)
                    (cond_transport hext₁ hwf hesz hcond)
                · rename_i hidv
                  exact absurd (by omega : i - d < vs.size) hidv
              · -- i - d ≥ k: lowered past the whole live prefix
                rename_i hidk
                rcases hI : st.intern (.bvar (i - k)) with ⟨ri, sti⟩
                rw [hI] at hgo
                cases hgo
                have hwfI : (st.intern (.bvar (i - k))).2.WF :=
                  intern_wf hwf (by simp [ENode.children]) (by simp [ENode.levels])
                have hextI : Ext st (st.intern (.bvar (i - k))).2 :=
                  intern_ext _ _
                have hdI : (st.intern (.bvar (i - k))).2.denote
                      (st.intern (.bvar (i - k))).1
                    = denoteNode st.denote st.denoteL (.bvar (i - k)) :=
                  intern_denote hwf (by simp [ENode.children])
                rw [hI] at hwfI hextI hdI
                have hcond : ∀ x, st.denote e = some x →
                    sti.denote ri
                      = some (x.instantiateList (ws.take k) d) := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  rw [hdI]
                  rw [Expr.instantiateList, if_neg hid,
                    dif_neg (by omega : ¬ i - d < (ws.take k).length),
                    htklen]
                  rfl
                refine ⟨hwfI, hextI, ?_, hcond⟩
                exact (hinv.mono hextI hwf).insert
                  (Nat.lt_of_lt_of_le hesz hextI.size_le)
                  (cond_transport hextI hwf hesz hcond)
          | fvar idx nm t =>
            dsimp only at hgo
            cases hgo
            obtain ⟨xt, hxt⟩ := denote_total hwf t
              (Nat.lt_trans (hcl t (by simp [ENode.children])) hesz)
            have hx : st.denote e = some (.fvar idx nm xt) := by
              rw [hde, denoteNode, hxt]; rfl
            have hcond : ∀ x, st.denote e = some x →
                st.denote e = some (x.instantiateList (ws.take k) d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.instantiateList] using hx
            exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
          | sort u =>
            dsimp only at hgo
            cases hgo
            obtain ⟨lu, hlu⟩ := denoteL_total hwf u
              (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
            have hx : st.denote e = some (.sort lu) := by
              rw [hde, denoteNode, hlu]; rfl
            have hcond : ∀ x, st.denote e = some x →
                st.denote e = some (x.instantiateList (ws.take k) d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.instantiateList] using hx
            exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
          | const nm us =>
            dsimp only at hgo
            cases hgo
            obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
              (fun v hv => hwf.levels_lt e _ hn v (by simp [ENode.levels, hv]))
            have hx : st.denote e = some (.const nm lus) := by
              rw [hde, denoteNode, hlus]; rfl
            have hcond : ∀ x, st.denote e = some x →
                st.denote e = some (x.instantiateList (ws.take k) d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.instantiateList] using hx
            exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
          | lit l =>
            dsimp only at hgo
            cases hgo
            have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
            have hcond : ∀ x, st.denote e = some x →
                st.denote e = some (x.instantiateList (ws.take k) d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.instantiateList] using hx
            exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
          | app f a =>
            dsimp only at hgo
            split at hgo
            case isFalse hguard =>
              exact absurd ⟨hcl f (by simp [ENode.children]),
                hcl a (by simp [ENode.children])⟩ hguard
            case isTrue hguard =>
              rcases h₁ : instantiateListIGo vs st bm0 memo f k d
                with ⟨f', st₁, memo₁⟩
              rw [h₁] at hgo
              rcases h₂ : instantiateListIGo vs st₁ bm0 memo₁ a k d
                with ⟨a', st₂, memo₂⟩
              rw [h₂] at hgo
              rcases h₃ : st₂.intern (.app f' a') with ⟨ri, st₃⟩
              rw [h₃] at hgo
              cases hgo
              obtain ⟨xf, hf⟩ := denote_total hwf f
                (Nat.lt_trans hguard.1 hesz)
              obtain ⟨xa, ha⟩ := denote_total hwf a
                (Nat.lt_trans hguard.2 hesz)
              have hx : st.denote e = some (.app xf xa) := by
                rw [hde, denoteNode, hf, ha]; rfl
              obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ :=
                ihe f hguard.1 hwf hvs hk hbm0 hinv h₁
              obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ :=
                ihe a hguard.2 hwf₁ (hvs.mono hext₁) hk (hbm0.mono hext₁ hwf) hinv₁ h₂
              have hf₂ : st₂.denote f'
                  = some (xf.instantiateList (ws.take k) d) :=
                denote_mono hext₂ (hden₁ xf hf)
              have ha₂ : st₂.denote a'
                  = some (xa.instantiateList (ws.take k) d) :=
                hden₂ xa (denote_mono hext₁ ha)
              have hcI : ∀ c ∈ (ENode.app f' a').children,
                  c < st₂.nodes.size := by
                simp only [ENode.children, List.mem_cons,
                  List.not_mem_nil, or_false]
                rintro c (rfl | rfl)
                · exact denote_lt_size hf₂
                · exact denote_lt_size ha₂
              have hwf₃ : (st₂.intern (.app f' a')).2.WF := intern_wf hwf₂ hcI (by simp [ENode.levels])
              have hext₃ : Ext st₂ (st₂.intern (.app f' a')).2 :=
                intern_ext _ _
              have hdI := intern_denote (n := .app f' a') hwf₂ hcI
              rw [h₃] at hwf₃ hext₃ hdI
              have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
              have hcond : ∀ x, st.denote e = some x →
                  st₃.denote ri
                    = some (x.instantiateList (ws.take k) d) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [hdI, denoteNode, hf₂, ha₂]
                simp [Expr.instantiateList]
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
              rcases h₁ : instantiateListIGo vs st bm0 memo ty k d
                with ⟨ty', st₁, memo₁⟩
              rw [h₁] at hgo
              rcases h₂ : instantiateListIGo vs st₁ bm0 memo₁ body k (d + 1)
                with ⟨body', st₂, memo₂⟩
              rw [h₂] at hgo
              rcases h₃ : st₂.intern (.lam nm ty' body' m) with ⟨ri, st₃⟩
              rw [h₃] at hgo
              cases hgo
              obtain ⟨xt, ht⟩ := denote_total hwf ty
                (Nat.lt_trans hguard.1 hesz)
              obtain ⟨xb, hb⟩ := denote_total hwf body
                (Nat.lt_trans hguard.2 hesz)
              obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
                (fun u hu => hwf.levels_lt e _ hn u
                  (by simpa [ENode.levels] using hu))
              have hx : st.denote e = some (.lam nm xt xb bm) := by
                rw [hde, denoteNode, ht, hb, hbm]; rfl
              obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ :=
                ihe ty hguard.1 hwf hvs hk hbm0 hinv h₁
              obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ :=
                ihe body hguard.2 hwf₁ (hvs.mono hext₁) hk (hbm0.mono hext₁ hwf) hinv₁ h₂
              have ht₂ : st₂.denote ty'
                  = some (xt.instantiateList (ws.take k) d) :=
                denote_mono hext₂ (hden₁ xt ht)
              have hb₂ : st₂.denote body'
                  = some (xb.instantiateList (ws.take k) (d + 1)) :=
                hden₂ xb (denote_mono hext₁ hb)
              have hcI : ∀ c ∈ (ENode.lam nm ty' body' m).children,
                  c < st₂.nodes.size := by
                simp only [ENode.children, List.mem_cons,
                  List.not_mem_nil, or_false]
                rintro c (rfl | rfl)
                · exact denote_lt_size ht₂
                · exact denote_lt_size hb₂
              have hlvI : ∀ u ∈ (ENode.lam nm ty' body' m).levels,
                  u < st₂.lnodes.size := fun u hu =>
                Nat.lt_of_lt_of_le
                  (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                  (hext₁.trans hext₂).lsize_le
              have hwf₃ : (st₂.intern (.lam nm ty' body' m)).2.WF :=
                intern_wf hwf₂ hcI hlvI
              have hext₃ : Ext st₂ (st₂.intern (.lam nm ty' body' m)).2 :=
                intern_ext _ _
              have hdI := intern_denote (n := .lam nm ty' body' m) hwf₂ hcI
              rw [h₃] at hwf₃ hext₃ hdI
              have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
              have hcond : ∀ x, st.denote e = some x →
                  st₃.denote ri
                    = some (x.instantiateList (ws.take k) d) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [hdI, denoteNode, ht₂, hb₂,
                  denoteBM_mono (hext₁.trans hext₂) hbm]
                simp [Expr.instantiateList]
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
              rcases h₁ : instantiateListIGo vs st bm0 memo ty k d
                with ⟨ty', st₁, memo₁⟩
              rw [h₁] at hgo
              rcases h₂ : instantiateListIGo vs st₁ bm0 memo₁ body k (d + 1)
                with ⟨body', st₂, memo₂⟩
              rw [h₂] at hgo
              rcases h₃ : st₂.intern (.forallE nm ty' body' m) with ⟨ri, st₃⟩
              rw [h₃] at hgo
              cases hgo
              obtain ⟨xt, ht⟩ := denote_total hwf ty
                (Nat.lt_trans hguard.1 hesz)
              obtain ⟨xb, hb⟩ := denote_total hwf body
                (Nat.lt_trans hguard.2 hesz)
              obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
                (fun u hu => hwf.levels_lt e _ hn u
                  (by simpa [ENode.levels] using hu))
              have hx : st.denote e = some (.forallE nm xt xb bm) := by
                rw [hde, denoteNode, ht, hb, hbm]; rfl
              obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ :=
                ihe ty hguard.1 hwf hvs hk hbm0 hinv h₁
              obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ :=
                ihe body hguard.2 hwf₁ (hvs.mono hext₁) hk (hbm0.mono hext₁ hwf) hinv₁ h₂
              have ht₂ : st₂.denote ty'
                  = some (xt.instantiateList (ws.take k) d) :=
                denote_mono hext₂ (hden₁ xt ht)
              have hb₂ : st₂.denote body'
                  = some (xb.instantiateList (ws.take k) (d + 1)) :=
                hden₂ xb (denote_mono hext₁ hb)
              have hcI : ∀ c ∈ (ENode.forallE nm ty' body' m).children,
                  c < st₂.nodes.size := by
                simp only [ENode.children, List.mem_cons,
                  List.not_mem_nil, or_false]
                rintro c (rfl | rfl)
                · exact denote_lt_size ht₂
                · exact denote_lt_size hb₂
              have hlvI : ∀ u ∈ (ENode.forallE nm ty' body' m).levels,
                  u < st₂.lnodes.size := fun u hu =>
                Nat.lt_of_lt_of_le
                  (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                  (hext₁.trans hext₂).lsize_le
              have hwf₃ : (st₂.intern (.forallE nm ty' body' m)).2.WF :=
                intern_wf hwf₂ hcI hlvI
              have hext₃ : Ext st₂ (st₂.intern (.forallE nm ty' body' m)).2 :=
                intern_ext _ _
              have hdI := intern_denote (n := .forallE nm ty' body' m)
                hwf₂ hcI
              rw [h₃] at hwf₃ hext₃ hdI
              have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
              have hcond : ∀ x, st.denote e = some x →
                  st₃.denote ri
                    = some (x.instantiateList (ws.take k) d) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [hdI, denoteNode, ht₂, hb₂,
                  denoteBM_mono (hext₁.trans hext₂) hbm]
                simp [Expr.instantiateList]
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
              rcases h₁ : instantiateListIGo vs st bm0 memo ty k d
                with ⟨ty', st₁, memo₁⟩
              rw [h₁] at hgo
              rcases h₂ : instantiateListIGo vs st₁ bm0 memo₁ val k d
                with ⟨val', st₂, memo₂⟩
              rw [h₂] at hgo
              rcases h₃ : instantiateListIGo vs st₂ bm0 memo₂ body k (d + 1)
                with ⟨body', st₃, memo₃⟩
              rw [h₃] at hgo
              rcases h₄ : st₃.intern (.letE nm ty' val' body') with ⟨ri, st₄⟩
              rw [h₄] at hgo
              cases hgo
              obtain ⟨xt, ht⟩ := denote_total hwf ty
                (Nat.lt_trans hguard.1 hesz)
              obtain ⟨xv, hv'⟩ := denote_total hwf val
                (Nat.lt_trans hguard.2.1 hesz)
              obtain ⟨xb, hb⟩ := denote_total hwf body
                (Nat.lt_trans hguard.2.2 hesz)
              have hx : st.denote e = some (.letE nm xt xv xb) := by
                rw [hde, denoteNode, ht, hv', hb]; rfl
              obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ :=
                ihe ty hguard.1 hwf hvs hk hbm0 hinv h₁
              obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ :=
                ihe val hguard.2.1 hwf₁ (hvs.mono hext₁) hk (hbm0.mono hext₁ hwf) hinv₁ h₂
              obtain ⟨hwf₃, hext₃, hinv₃, hden₃⟩ :=
                ihe body hguard.2.2 hwf₂ (hvs.mono (hext₁.trans hext₂))
                  hk (hbm0.mono (hext₁.trans hext₂) hwf) hinv₂ h₃
              have ht₃ : st₃.denote ty'
                  = some (xt.instantiateList (ws.take k) d) :=
                denote_mono (hext₂.trans hext₃) (hden₁ xt ht)
              have hv₃ : st₃.denote val'
                  = some (xv.instantiateList (ws.take k) d) :=
                denote_mono hext₃ (hden₂ xv (denote_mono hext₁ hv'))
              have hb₃ : st₃.denote body'
                  = some (xb.instantiateList (ws.take k) (d + 1)) :=
                hden₃ xb (denote_mono (hext₁.trans hext₂) hb)
              have hcI : ∀ c ∈ (ENode.letE nm ty' val' body').children,
                  c < st₃.nodes.size := by
                simp only [ENode.children, List.mem_cons,
                  List.not_mem_nil, or_false]
                rintro c (rfl | rfl | rfl)
                · exact denote_lt_size ht₃
                · exact denote_lt_size hv₃
                · exact denote_lt_size hb₃
              have hwf₄ : (st₃.intern (.letE nm ty' val' body')).2.WF :=
                intern_wf hwf₃ hcI (by simp [ENode.levels])
              have hext₄ : Ext st₃ (st₃.intern (.letE nm ty' val' body')).2 :=
                intern_ext _ _
              have hdI := intern_denote (n := .letE nm ty' val' body')
                hwf₃ hcI
              rw [h₄] at hwf₄ hext₄ hdI
              have hextAll : Ext st st₄ :=
                hext₁.trans (hext₂.trans (hext₃.trans hext₄))
              have hcond : ∀ x, st.denote e = some x →
                  st₄.denote ri
                    = some (x.instantiateList (ws.take k) d) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [hdI, denoteNode, ht₃, hv₃, hb₃]
                simp [Expr.instantiateList]
              refine ⟨hwf₄, hextAll, ?_, hcond⟩
              exact (hinv₃.mono hext₄ hwf₃).insert
                (Nat.lt_of_lt_of_le hesz hextAll.size_le)
                (cond_transport hextAll hwf hesz hcond)
          | proj s i sub =>
            dsimp only at hgo
            split at hgo
            case isFalse hguard =>
              exact absurd (hcl sub (by simp [ENode.children])) hguard
            case isTrue hguard =>
              rcases h₁ : instantiateListIGo vs st bm0 memo sub k d
                with ⟨sub', st₁, memo₁⟩
              rw [h₁] at hgo
              rcases h₂ : st₁.intern (.proj s i sub') with ⟨ri, st₂⟩
              rw [h₂] at hgo
              cases hgo
              obtain ⟨xs, hxs⟩ := denote_total hwf sub
                (Nat.lt_trans hguard hesz)
              have hx : st.denote e = some (.proj s i xs) := by
                rw [hde, denoteNode, hxs]; rfl
              obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ :=
                ihe sub hguard hwf hvs hk hbm0 hinv h₁
              have hs₁ : st₁.denote sub'
                  = some (xs.instantiateList (ws.take k) d) :=
                hden₁ xs hxs
              have hcI : ∀ c ∈ (ENode.proj s i sub').children,
                  c < st₁.nodes.size := by
                simp only [ENode.children, List.mem_cons,
                  List.not_mem_nil, or_false]
                rintro c rfl
                exact denote_lt_size hs₁
              have hwf₂ : (st₁.intern (.proj s i sub')).2.WF :=
                intern_wf hwf₁ hcI (by simp [ENode.levels])
              have hext₂ : Ext st₁ (st₁.intern (.proj s i sub')).2 :=
                intern_ext _ _
              have hdI := intern_denote (n := .proj s i sub') hwf₁ hcI
              rw [h₂] at hwf₂ hext₂ hdI
              have hextAll : Ext st st₂ := hext₁.trans hext₂
              have hcond : ∀ x, st.denote e = some x →
                  st₂.denote ri
                    = some (x.instantiateList (ws.take k) d) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [hdI, denoteNode, hs₁]
                simp [Expr.instantiateList]
              refine ⟨hwf₂, hextAll, ?_, hcond⟩
              exact (hinv₁.mono hext₂ hwf₁).insert
                (Nat.lt_of_lt_of_le hesz hextAll.size_le)
                (cond_transport hextAll hwf hesz hcond)

/-- `instantiateListI` commutes with `denote`: the result denotes
`Expr.instantiateList` of the denotations, on an extended well-formed
store. -/
theorem instantiateListI_spec {st : EStore} {e : EIdx} {vs : List EIdx}
    {d : Nat} {x : Expr} {ws : List Expr} {bm0 : EStore.BMemo}
    (hwf : st.WF) (he : st.denote e = some x) (hvs : DenL st vs ws)
    (hbm0 : EStore.BoundMemoInv st bm0 := by
      exact EStore.BoundMemoInv.empty) :
    (st.instantiateListI e vs d bm0).2.WF ∧
      Ext st (st.instantiateListI e vs d bm0).2 ∧
      (st.instantiateListI e vs d bm0).2.denote
          (st.instantiateListI e vs d bm0).1
        = some (x.instantiateList ws d) := by
  match vs, ws, hvs with
  | [], [], _ =>
    simp only [instantiateListI, Expr.instantiateList_nil]
    exact ⟨hwf, Ext.refl st, he⟩
  | v :: vs', w :: ws', hvs =>
    have htl : (v :: vs').toArray.toList = v :: vs' := by simp
    have hvs' : DenL st (v :: vs').toArray.toList (w :: ws') := by
      rw [htl]; exact hvs
    rcases hgo : instantiateListIGo (v :: vs').toArray st bm0 {} e
        (v :: vs').toArray.size d with ⟨r, st', memo'⟩
    obtain ⟨hwf', hext', -, hcond⟩ :=
      instantiateListIGo_spec (vs := (v :: vs').toArray)
        (ws := w :: ws') _ e hwf hvs' (Nat.le_refl _) hbm0
        MemoNLInv.empty hgo
    have hlen : (w :: ws').length = (v :: vs').toArray.size := by
      simpa using hvs.length_eq.symm
    have htake : (w :: ws').take (v :: vs').toArray.size = w :: ws' := by
      rw [← hlen, List.take_length]
    simp only [instantiateListI, hgo]
    refine ⟨hwf', hext', ?_⟩
    have := hcond x he
    rwa [htake] at this

theorem mkAppNI_spec :
    ∀ {args : List EIdx} {xs : List Expr} {st : EStore}, st.WF →
      ∀ {f : EIdx} {x : Expr}, st.denote f = some x → DenL st args xs →
      (st.mkAppNI f args).2.WF ∧ Ext st (st.mkAppNI f args).2 ∧
        (st.mkAppNI f args).2.denote (st.mkAppNI f args).1
          = some (Expr.mkAppN x xs)
  | [], xs, st, hwf, f, x, hf, hargs => by
    match xs, hargs with
    | [], _ => exact ⟨hwf, Ext.refl st, hf⟩
  | a :: as, xs, st, hwf, f, x, hf, hargs => by
    match xs, hargs with
    | xa :: xs, ⟨ha, hs⟩ =>
      have hd : denoteNode st.denote st.denoteL (.app f a)
          = some (.app x xa) := by
        rw [denoteNode, hf, ha]; rfl
      obtain ⟨hwf₁, hext₁, hfa⟩ := intern_spec hwf hd
      rw [show st.mkAppNI f (a :: as) =
        (st.intern (.app f a)).2.mkAppNI (st.intern (.app f a)).1 as from rfl]
      obtain ⟨hwf₂, hext₂, hres⟩ :=
        mkAppNI_spec (args := as) (xs := xs) hwf₁ hfa (hs.mono hext₁)
      exact ⟨hwf₂, hext₁.trans hext₂, hres⟩

theorem instSpineChainI_spec {bm0 : EStore.BMemo} :
    ∀ {args : List EIdx} {xs : List Expr} {st : EStore}, st.WF →
      EStore.BoundMemoInv st bm0 →
      ∀ {t : Nat} {e : EIdx} {x : Expr},
      st.denote e = some x → DenL st args xs →
      (st.instSpineChainI bm0 args t e).2.WF ∧
        Ext st (st.instSpineChainI bm0 args t e).2 ∧
        (st.instSpineChainI bm0 args t e).2.denote
            (st.instSpineChainI bm0 args t e).1
          = some (Expr.instSpine xs t x)
  | [], xs, st, hwf, _hbm0, t, e, x, he, hargs => by
    match xs, hargs with
    | [], _ => exact ⟨hwf, Ext.refl st, he⟩
  | a :: as, xs, st, hwf, hbm0, t, e, x, he, hargs => by
    match xs, hargs with
    | xa :: xs, ⟨ha, hs⟩ =>
      obtain ⟨hwf₁, hext₁, he'⟩ := instantiate1I_spec (d := t) hwf he ha hbm0
      rw [show st.instSpineChainI bm0 (a :: as) t e =
        (st.instantiate1I e a t bm0).2.instSpineChainI bm0 as (t - 1)
          (st.instantiate1I e a t bm0).1 from rfl]
      obtain ⟨hwf₂, hext₂, hres⟩ :=
        instSpineChainI_spec (args := as) (xs := xs) hwf₁
          (hbm0.mono hext₁ hwf) he' (hs.mono hext₁)
      exact ⟨hwf₂, hext₁.trans hext₂, hres⟩

theorem instSpineI_spec {args : List EIdx} {xs : List Expr} {st : EStore}
    {bm0 : EStore.BMemo}
    (hwf : st.WF) {t : Nat} {e : EIdx} {x : Expr}
    (he : st.denote e = some x) (hargs : DenL st args xs)
    (hbm0 : EStore.BoundMemoInv st bm0 := by
      exact EStore.BoundMemoInv.empty) :
    (st.instSpineI args t e bm0).2.WF ∧
      Ext st (st.instSpineI args t e bm0).2 ∧
      (st.instSpineI args t e bm0).2.denote (st.instSpineI args t e bm0).1
        = some (Expr.instSpine xs t x) := by
  unfold instSpineI
  by_cases hlen : args.length = t + 1
  · rw [if_pos hlen]
    have hxlen : xs.length = t + 1 := hargs.length_eq ▸ hlen
    obtain ⟨hwf', hext', hden⟩ :=
      instantiateListI_spec (d := 0) hwf he hargs.reverse hbm0
    exact ⟨hwf', hext',
      Expr.instSpine_eq_instantiateList xs t x hxlen ▸ hden⟩
  · rw [if_neg hlen]
    exact instSpineChainI_spec hwf hbm0 he hargs

/-- Relation of an optional index to an optional expression under a
store. -/
def OptDen (st : EStore) : Option EIdx → Option Expr → Prop
  | none, none => True
  | some i, some x => st.denote i = some x
  | _, _ => False

theorem OptDen.mono {st st' : EStore} (hext : Ext st st') :
    ∀ {o : Option EIdx} {ox : Option Expr}, OptDen st o ox →
      OptDen st' o ox
  | none, none, _ => trivial
  | some _, some _, h => denote_mono hext h
  | none, some _, h | some _, none, h => nomatch h

theorem piResidualAccI_spec {bm0 : EStore.BMemo} :
    ∀ {as : List EIdx} {xs : List Expr} {acc : List EIdx} {ws : List Expr}
      {st : EStore}, st.WF → EStore.BoundMemoInv st bm0 →
      ∀ {e : EIdx} {x : Expr},
      st.denote e = some x → DenL st acc ws → DenL st as xs →
      (st.piResidualAccI bm0 acc e as).2.WF ∧
        Ext st (st.piResidualAccI bm0 acc e as).2 ∧
        OptDen (st.piResidualAccI bm0 acc e as).2
          (st.piResidualAccI bm0 acc e as).1
          (piResidual (x.instantiateList ws) xs)
  | [], xs, acc, ws, st, hwf, hbm0, e, x, he, hacc, hargs => by
    match xs, hargs with
    | [], _ =>
      obtain ⟨hwf', hext', hden⟩ :=
        instantiateListI_spec (d := 0) hwf he hacc hbm0
      rw [piResidualAccI.eq_def]
      dsimp only
      exact ⟨hwf', hext', hden⟩
  | a :: as, xs, acc, ws, st, hwf, hbm0, e, x, he, hacc, hargs => by
    match xs, hargs with
    | xa :: xs, ⟨ha, hs⟩ =>
      obtain ⟨n, hn, hc, hd⟩ := denote_some_inv he
      cases n with
      | forallE nm t b m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, ht, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨eb, hb, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨bm, hbm', rfl⟩ := hd
        rw [piResidualAccI.eq_def]
        dsimp only
        rw [hn]
        dsimp only
        simp only [Expr.instantiateList]
        rw [show piResidual
            (.forallE nm (et.instantiateList ws 0)
              (eb.instantiateList ws 1) bm) (xa :: xs) =
          piResidual ((eb.instantiateList ws 1).instantiate1 xa) xs
          from rfl,
          ← Expr.instantiateList_cons]
        exact piResidualAccI_spec (as := as) (xs := xs) hwf hbm0 hb
          ⟨ha, hacc⟩ hs
      | bvar i =>
        cases hd
        rw [piResidualAccI.eq_def]
        dsimp only
        rw [hn]
        dsimp only
        match acc, ws, hacc with
        | [], [], _ =>
          rw [Expr.instantiateList_nil]
          exact ⟨hwf, Ext.refl st, trivial⟩
        | a' :: acc', w :: ws', hacc =>
          obtain ⟨hwf₁, hext₁, hden₁⟩ :=
            instantiateListI_spec (d := 0) hwf he hacc hbm0
          have := piResidualAccI_spec (as := a :: as) (xs := xa :: xs)
            (acc := []) (ws := []) hwf₁ (hbm0.mono hext₁ hwf) hden₁ DenL.nil
            (DenL.mono hext₁ ⟨ha, hs⟩)
          rw [Expr.instantiateList_nil] at this
          obtain ⟨hwf₂, hext₂, hres⟩ := this
          exact ⟨hwf₂, hext₁.trans hext₂, hres⟩
      | app f a' =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨ef, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨ea, _, rfl⟩ := hd
        rw [piResidualAccI.eq_def]
        dsimp only
        rw [hn]
        simp only [Expr.instantiateList]
        exact ⟨hwf, Ext.refl st, trivial⟩
      | sort u =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨lu, _, rfl⟩ := hd
        rw [piResidualAccI.eq_def]
        dsimp only
        rw [hn]
        simp only [Expr.instantiateList]
        exact ⟨hwf, Ext.refl st, trivial⟩
      | const nm us =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨lus, _, rfl⟩ := hd
        rw [piResidualAccI.eq_def]
        dsimp only
        rw [hn]
        simp only [Expr.instantiateList]
        exact ⟨hwf, Ext.refl st, trivial⟩
      | lit l =>
        cases hd
        rw [piResidualAccI.eq_def]
        dsimp only
        rw [hn]
        simp only [Expr.instantiateList]
        exact ⟨hwf, Ext.refl st, trivial⟩
      | fvar idx nm t =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨t', _, rfl⟩ := hd
        rw [piResidualAccI.eq_def]
        dsimp only
        rw [hn]
        simp only [Expr.instantiateList]
        exact ⟨hwf, Ext.refl st, trivial⟩
      | lam nm t b m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, _, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨eb, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨bm, hbm', rfl⟩ := hd
        rw [piResidualAccI.eq_def]
        dsimp only
        rw [hn]
        simp only [Expr.instantiateList]
        exact ⟨hwf, Ext.refl st, trivial⟩
      | letE nm t v b =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨et, _, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨ev, _, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨eb, _, rfl⟩ := hd
        rw [piResidualAccI.eq_def]
        dsimp only
        rw [hn]
        simp only [Expr.instantiateList]
        exact ⟨hwf, Ext.refl st, trivial⟩
      | proj s j e' =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨ee, _, rfl⟩ := hd
        rw [piResidualAccI.eq_def]
        dsimp only
        rw [hn]
        simp only [Expr.instantiateList]
        exact ⟨hwf, Ext.refl st, trivial⟩
termination_by as _ acc => (as.length, acc.length)
decreasing_by
  · apply Prod.Lex.right' <;> simp
  · apply Prod.Lex.left; simp

theorem piResidualI_spec {bm0 : EStore.BMemo} :
    ∀ {args : List EIdx} {xs : List Expr} {st : EStore}, st.WF →
      EStore.BoundMemoInv st bm0 →
      ∀ {e : EIdx} {x : Expr},
      st.denote e = some x → DenL st args xs →
      (st.piResidualI e args bm0).2.WF ∧
        Ext st (st.piResidualI e args bm0).2 ∧
        OptDen (st.piResidualI e args bm0).2 (st.piResidualI e args bm0).1
          (piResidual x xs) := by
  intro args xs st hwf hbm0 e x he hargs
  have := piResidualAccI_spec (acc := []) (ws := []) hwf hbm0 he
    DenL.nil hargs
  rw [Expr.instantiateList_nil] at this
  exact this

/-- `Expr.instPis` and the core's `piResidual` are the same function. -/
theorem instPis_eq_piResidual :
    ∀ (e : Expr) (as : List Expr), e.instPis as = piResidual e as
  | _, [] => rfl
  | .forallE _ _ b _, a :: as => instPis_eq_piResidual (b.instantiate1 a) as
  | .bvar _, _ :: _ | .fvar _ _ _, _ :: _ | .sort _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _ _ _, _ :: _
  | .letE _ _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

theorem pisToLamsI_spec :
    ∀ {k : Nat} {st : EStore}, st.WF →
      ∀ {e body : EIdx} {x xb : Expr},
      st.denote e = some x → st.denote body = some xb →
      (st.pisToLamsI k e body).2.WF ∧ Ext st (st.pisToLamsI k e body).2 ∧
        OptDen (st.pisToLamsI k e body).2 (st.pisToLamsI k e body).1
          (Expr.pisToLams k x xb)
  | 0, st, hwf, e, body, x, xb, he, hb => ⟨hwf, Ext.refl st, hb⟩
  | k + 1, st, hwf, e, body, x, xb, he, hb => by
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv he
    cases n with
    | forallE nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, ht, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨eb, hbb, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨bm, hbm', rfl⟩ := hd
      obtain ⟨bi', cod'⟩ := bm
      have hbi : bi' = m.bi := by simpa using denoteBM_bi hbm'
      subst hbi
      obtain ⟨hwf₁, hext₁, hres₁⟩ :=
        pisToLamsI_spec (k := k) hwf hbb hb (e := b) (body := body)
      rw [pisToLamsI, hn]
      dsimp only
      rw [show Expr.pisToLams (k + 1) (.forallE nm et eb ⟨m.bi, cod'⟩) xb =
        (Expr.pisToLams k eb xb).map (fun bx => .lam nm et bx ⟨m.bi, none⟩)
        from rfl]
      rcases hgo : st.pisToLamsI k b body with ⟨o, st₁⟩
      rw [hgo] at hres₁ hwf₁ hext₁
      cases o with
      | none =>
        cases hox : Expr.pisToLams k eb xb with
        | none => exact ⟨hwf₁, hext₁, by simp [OptDen]⟩
        | some bx => rw [hox] at hres₁; exact nomatch hres₁
      | some bidx =>
        cases hox : Expr.pisToLams k eb xb with
        | none => rw [hox] at hres₁; exact nomatch hres₁
        | some bx =>
          rw [hox] at hres₁
          have hd' : denoteNode st₁.denote st₁.denoteL
                (.lam nm t bidx ⟨m.bi, none⟩)
              = some (.lam nm et bx ⟨m.bi, none⟩) := by
            rw [denoteNode, denote_mono hext₁ ht, hres₁]; rfl
          obtain ⟨hwf₂, hext₂, hres₂⟩ := intern_spec hwf₁ hd'
          exact ⟨hwf₂, hext₁.trans hext₂, hres₂⟩
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨ef, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨ea, _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | bvar i => cases hd; rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨lu, _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | const nm us =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨lus, _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | lit l => cases hd; rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | fvar idx nm t =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨t', _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | lam nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨eb, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨bm, _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | letE nm t v b =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨ev, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩
    | proj s j e' =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨ee, _, rfl⟩ := hd
      rw [pisToLamsI, hn]; exact ⟨hwf, Ext.refl st, trivial⟩

theorem stripPisBodyI_spec {st : EStore} (_hwf : st.WF) :
    ∀ {k : Nat} {e : EIdx} {x : Expr}, st.denote e = some x →
      OptDen st (st.stripPisBodyI k e) ((x.stripPis k).map (·.2)) := by
  intro k
  induction k with
  | zero =>
    intro e x he
    simpa [stripPisBodyI, Expr.stripPis, OptDen] using he
  | succ k ih =>
    intro e x he
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv he
    cases n with
    | forallE nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, ht, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨eb, hbb, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨bm, hbm', rfl⟩ := hd
      have := ih (e := b) hbb
      rw [stripPisBodyI, hn]
      dsimp only
      rw [show Expr.stripPis (k + 1) (.forallE nm et eb bm) =
        (eb.stripPis k).map (fun p => ((nm, et, bm) :: p.1, p.2)) from rfl]
      cases hs : eb.stripPis k with
      | none => rw [hs] at this; simpa using this
      | some p => rw [hs] at this; simpa using this
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨ef, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨ea, _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial
    | bvar i => cases hd; rw [stripPisBodyI, hn]; exact trivial
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨lu, _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial
    | const nm us =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨lus, _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial
    | lit l => cases hd; rw [stripPisBodyI, hn]; exact trivial
    | fvar idx nm t =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨t', _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial
    | lam nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨eb, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨bm, _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial
    | letE nm t v b =>
      rw [denoteNode, Option.bind_eq_some_iff] at hd
      obtain ⟨et, _, hd⟩ := hd
      rw [Option.bind_eq_some_iff] at hd
      obtain ⟨ev, _, hd⟩ := hd
      rw [Option.map_eq_some_iff] at hd
      obtain ⟨eb, _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial
    | proj s j e' =>
      rw [denoteNode, Option.map_eq_some_iff] at hd
      obtain ⟨ee, _, rfl⟩ := hd
      rw [stripPisBodyI, hn]; exact trivial

/-! ## Readback -/

/-- Invariant of the readback memo: every entry is the denotation. -/
def RInv (st : EStore) (memo : Std.HashMap EIdx Expr) : Prop :=
  ∀ i x, memo[i]? = some x → st.denote i = some x

theorem RInv.empty {st : EStore} : RInv st {} := by
  intro i x h
  simp at h

theorem RInv.insert {st : EStore} {memo : Std.HashMap EIdx Expr}
    {e : EIdx} {x : Expr} (h : RInv st memo) (hx : st.denote e = some x) :
    RInv st (memo.insert e x) := by
  intro i y hy
  rw [Std.HashMap.getElem?_insert] at hy
  by_cases hk : e = i
  · subst hk
    rw [if_pos (by simp)] at hy
    cases hy
    exact hx
  · rw [if_neg (by simpa using hk)] at hy
    exact h i y hy

/-- Invariant of the level readback memo. -/
def RLInv (st : EStore) (memo : Std.HashMap LIdx Level) : Prop :=
  ∀ u l, memo[u]? = some l → st.denoteL u = some l

theorem RLInv.empty {st : EStore} : RLInv st {} := by
  intro u l h
  simp at h

theorem RLInv.insert {st : EStore} {memo : Std.HashMap LIdx Level}
    {u : LIdx} {l : Level} (h : RLInv st memo) (hl : st.denoteL u = some l) :
    RLInv st (memo.insert u l) := by
  intro v y hy
  rw [Std.HashMap.getElem?_insert] at hy
  by_cases hk : u = v
  · subst hk
    rw [if_pos (by simp)] at hy
    cases hy
    exact hl
  · rw [if_neg (by simpa using hk)] at hy
    exact h v y hy

theorem readbackLGo_spec {st : EStore} :
    ∀ (u : LIdx) {l : Level} {memo : Std.HashMap LIdx Level}
      {r : Option Level} {memo' : Std.HashMap LIdx Level},
      st.denoteL u = some l → RLInv st memo →
      readbackLGo st memo u = (r, memo') →
      r = some l ∧ RLInv st memo' := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro l memo r memo' hl hinv hgo
    obtain ⟨n, hn, hc, hd⟩ := denoteL_some_inv hl
    unfold readbackLGo at hgo
    cases hm : memo[u]? with
    | some y =>
      rw [hm] at hgo
      injection hgo with h1 h2
      subst h1; subst h2
      have := hinv u y hm
      rw [hl] at this
      exact ⟨by injection this with h; rw [h], hinv⟩
    | none =>
      rw [hm, hn] at hgo
      cases n with
      | zero =>
        cases hd
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv.insert hl⟩
      | param p =>
        cases hd
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv.insert hl⟩
      | succ v =>
        rw [denoteLNode, Option.map_eq_some_iff] at hd
        obtain ⟨xl, hxl, rfl⟩ := hd
        have hlt : v < u := hc v (by simp [LNode.children])
        dsimp only at hgo
        rw [dif_pos hlt] at hgo
        rcases hgv : readbackLGo st memo v with ⟨rv, memo₁⟩
        obtain ⟨rfl, hinv₁⟩ := ih v hlt hxl hinv hgv
        rw [hgv] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv₁.insert hl⟩
      | max a b =>
        rw [denoteLNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xa, hxa, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨xb, hxb, rfl⟩ := hd
        have hlta : a < u := hc a (by simp [LNode.children])
        have hltb : b < u := hc b (by simp [LNode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hlta, hltb⟩] at hgo
        rcases hga : readbackLGo st memo a with ⟨ra, memo₁⟩
        obtain ⟨rfl, hinv₁⟩ := ih a hlta hxa hinv hga
        rcases hgb : readbackLGo st memo₁ b with ⟨rb, memo₂⟩
        obtain ⟨rfl, hinv₂⟩ := ih b hltb hxb hinv₁ hgb
        rw [hga] at hgo
        dsimp only at hgo
        rw [hgb] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv₂.insert hl⟩
      | imax a b =>
        rw [denoteLNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xa, hxa, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨xb, hxb, rfl⟩ := hd
        have hlta : a < u := hc a (by simp [LNode.children])
        have hltb : b < u := hc b (by simp [LNode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hlta, hltb⟩] at hgo
        rcases hga : readbackLGo st memo a with ⟨ra, memo₁⟩
        obtain ⟨rfl, hinv₁⟩ := ih a hlta hxa hinv hga
        rcases hgb : readbackLGo st memo₁ b with ⟨rb, memo₂⟩
        obtain ⟨rfl, hinv₂⟩ := ih b hltb hxb hinv₁ hgb
        rw [hga] at hgo
        dsimp only at hgo
        rw [hgb] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        subst h1; subst h2
        exact ⟨rfl, hinv₂.insert hl⟩

/-- On a well-formed store, `readbackL` computes the level
denotation. -/
theorem readbackL_spec {st : EStore} {u : LIdx} {l : Level}
    (hl : st.denoteL u = some l) : st.readbackL u = some l := by
  rcases hgo : readbackLGo st {} u with ⟨r, memo'⟩
  obtain ⟨rfl, -⟩ := readbackLGo_spec u hl RLInv.empty hgo
  rw [readbackL, hgo]

theorem readbackLList_spec {st : EStore} :
    ∀ (us : List LIdx) {ls : List Level} {memo : Std.HashMap LIdx Level}
      {r : Option (List Level)} {memo' : Std.HashMap LIdx Level},
      denoteLList st.denoteL us = some ls → RLInv st memo →
      readbackLList st memo us = (r, memo') →
      r = some ls ∧ RLInv st memo' := by
  intro us
  induction us with
  | nil =>
    intro ls memo r memo' hls hinv hgo
    cases hls
    cases hgo
    exact ⟨rfl, hinv⟩
  | cons u us ih =>
    intro ls memo r memo' hls hinv hgo
    simp only [denoteLList, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hls
    obtain ⟨l, hl, ls', hls', rfl⟩ := hls
    dsimp only [readbackLList] at hgo
    rcases hg₁ : readbackLGo st memo u with ⟨r₁, memo₁⟩
    rw [hg₁] at hgo
    obtain ⟨rfl, hinv₁⟩ := readbackLGo_spec u hl hinv hg₁
    dsimp only at hgo
    rcases hg₂ : readbackLList st memo₁ us with ⟨r₂, memo₂⟩
    rw [hg₂] at hgo
    obtain ⟨rfl, hinv₂⟩ := ih hls' hinv₁ hg₂
    dsimp only at hgo
    injection hgo with h1 h2
    subst h1; subst h2
    exact ⟨rfl, hinv₂⟩

theorem readbackBM_spec {st : EStore} {m : IBinderMeta} {bm : BinderMeta}
    {memo : Std.HashMap LIdx Level} {r : Option BinderMeta}
    {memo' : Std.HashMap LIdx Level}
    (hbm : denoteBM st.denoteL m = some bm) (hinv : RLInv st memo)
    (hgo : readbackBM st memo m = (r, memo')) :
    r = some bm ∧ RLInv st memo' := by
  obtain ⟨bi, (_ | u)⟩ := m
  · simp only [denoteBM, Option.some.injEq] at hbm
    subst hbm
    cases hgo
    exact ⟨rfl, hinv⟩
  · simp only [denoteBM, Option.map_eq_some_iff] at hbm
    obtain ⟨l, hl, rfl⟩ := hbm
    dsimp only [readbackBM] at hgo
    rcases hg : readbackLGo st memo u with ⟨r₁, memo₁⟩
    rw [hg] at hgo
    obtain ⟨rfl, hinv₁⟩ := readbackLGo_spec u hl hinv hg
    cases hgo
    exact ⟨rfl, hinv₁⟩

theorem readbackGo_spec {st : EStore} (_hwf : st.WF) :
    ∀ (e : EIdx) {x : Expr} {memo : Std.HashMap EIdx Expr}
      {lmemo : Std.HashMap LIdx Level}
      {r : Option Expr} {memo' : Std.HashMap EIdx Expr}
      {lmemo' : Std.HashMap LIdx Level},
      st.denote e = some x → RInv st memo → RLInv st lmemo →
      readbackGo st memo lmemo e = (r, memo', lmemo') →
      r = some x ∧ RInv st memo' ∧ RLInv st lmemo' := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro x memo lmemo r memo' lmemo' hx hinv hlinv hgo
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hx
    unfold readbackGo at hgo
    cases hm : memo[e]? with
    | some y =>
      rw [hm] at hgo
      injection hgo with h1 h2
      injection h2 with h2 h3
      subst h1; subst h2; subst h3
      have := hinv e y hm
      rw [hx] at this
      exact ⟨by injection this with h; rw [h], hinv, hlinv⟩
    | none =>
      rw [hm, hn] at hgo
      cases n with
      | bvar i =>
        cases hd
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨rfl, hinv.insert hx, hlinv⟩
      | sort u =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨lu, hlu, rfl⟩ := hd
        dsimp only at hgo
        rcases hg₁ : readbackLGo st lmemo u with ⟨r₁, lmemo₁⟩
        rw [hg₁] at hgo
        obtain ⟨rfl, hlinv₁⟩ := readbackLGo_spec u hlu hlinv hg₁
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨rfl, hinv.insert hx, hlinv₁⟩
      | const nm us =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨lus, hlus, rfl⟩ := hd
        dsimp only at hgo
        rcases hg₁ : readbackLList st lmemo us with ⟨r₁, lmemo₁⟩
        rw [hg₁] at hgo
        obtain ⟨rfl, hlinv₁⟩ := readbackLList_spec us hlus hlinv hg₁
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨rfl, hinv.insert hx, hlinv₁⟩
      | lit l =>
        cases hd
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨rfl, hinv.insert hx, hlinv⟩
      | fvar idx nm t =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨xt, ht, rfl⟩ := hd
        have hlt : t < e := hc t (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos hlt] at hgo
        rcases hgt : readbackGo st memo lmemo t with ⟨rt, memo₁, lmemo₁⟩
        obtain ⟨rfl, hinv₁, hlinv₁⟩ := ih t hlt ht hinv hlinv hgt
        rw [hgt] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨rfl, hinv₁.insert hx, hlinv₁⟩
      | app f a =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xf, hf, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨xa, ha, rfl⟩ := hd
        have hltf : f < e := hc f (by simp [ENode.children])
        have hlta : a < e := hc a (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltf, hlta⟩] at hgo
        rcases hgf : readbackGo st memo lmemo f with ⟨rf, memo₁, lmemo₁⟩
        obtain ⟨rfl, hinv₁, hlinv₁⟩ := ih f hltf hf hinv hlinv hgf
        rcases hga : readbackGo st memo₁ lmemo₁ a with ⟨ra, memo₂, lmemo₂⟩
        obtain ⟨rfl, hinv₂, hlinv₂⟩ := ih a hlta ha hinv₁ hlinv₁ hga
        rw [hgf] at hgo
        dsimp only at hgo
        rw [hga] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨rfl, hinv₂.insert hx, hlinv₂⟩
      | lam nm t b m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xt, ht, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨xb, hb, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨bm, hbm', rfl⟩ := hd
        have hltt : t < e := hc t (by simp [ENode.children])
        have hltb : b < e := hc b (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltt, hltb⟩] at hgo
        rcases hgt : readbackGo st memo lmemo t with ⟨rt, memo₁, lmemo₁⟩
        obtain ⟨rfl, hinv₁, hlinv₁⟩ := ih t hltt ht hinv hlinv hgt
        rcases hgb : readbackGo st memo₁ lmemo₁ b with ⟨rb, memo₂, lmemo₂⟩
        obtain ⟨rfl, hinv₂, hlinv₂⟩ := ih b hltb hb hinv₁ hlinv₁ hgb
        rcases hgm : readbackBM st lmemo₂ m with ⟨rm, lmemo₃⟩
        obtain ⟨rfl, hlinv₃⟩ := readbackBM_spec hbm' hlinv₂ hgm
        rw [hgt] at hgo
        dsimp only at hgo
        rw [hgb] at hgo
        dsimp only at hgo
        rw [hgm] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨rfl, hinv₂.insert hx, hlinv₃⟩
      | forallE nm t b m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xt, ht, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨xb, hb, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨bm, hbm', rfl⟩ := hd
        have hltt : t < e := hc t (by simp [ENode.children])
        have hltb : b < e := hc b (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltt, hltb⟩] at hgo
        rcases hgt : readbackGo st memo lmemo t with ⟨rt, memo₁, lmemo₁⟩
        obtain ⟨rfl, hinv₁, hlinv₁⟩ := ih t hltt ht hinv hlinv hgt
        rcases hgb : readbackGo st memo₁ lmemo₁ b with ⟨rb, memo₂, lmemo₂⟩
        obtain ⟨rfl, hinv₂, hlinv₂⟩ := ih b hltb hb hinv₁ hlinv₁ hgb
        rcases hgm : readbackBM st lmemo₂ m with ⟨rm, lmemo₃⟩
        obtain ⟨rfl, hlinv₃⟩ := readbackBM_spec hbm' hlinv₂ hgm
        rw [hgt] at hgo
        dsimp only at hgo
        rw [hgb] at hgo
        dsimp only at hgo
        rw [hgm] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨rfl, hinv₂.insert hx, hlinv₃⟩
      | letE nm t v b =>
        rw [denoteNode, Option.bind_eq_some_iff] at hd
        obtain ⟨xt, ht, hd⟩ := hd
        rw [Option.bind_eq_some_iff] at hd
        obtain ⟨xv, hv, hd⟩ := hd
        rw [Option.map_eq_some_iff] at hd
        obtain ⟨xb, hb, rfl⟩ := hd
        have hltt : t < e := hc t (by simp [ENode.children])
        have hltv : v < e := hc v (by simp [ENode.children])
        have hltb : b < e := hc b (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos ⟨hltt, hltv, hltb⟩] at hgo
        rcases hgt : readbackGo st memo lmemo t with ⟨rt, memo₁, lmemo₁⟩
        obtain ⟨rfl, hinv₁, hlinv₁⟩ := ih t hltt ht hinv hlinv hgt
        rcases hgv : readbackGo st memo₁ lmemo₁ v with ⟨rv, memo₂, lmemo₂⟩
        obtain ⟨rfl, hinv₂, hlinv₂⟩ := ih v hltv hv hinv₁ hlinv₁ hgv
        rcases hgb : readbackGo st memo₂ lmemo₂ b with ⟨rb, memo₃, lmemo₃⟩
        obtain ⟨rfl, hinv₃, hlinv₃⟩ := ih b hltb hb hinv₂ hlinv₂ hgb
        rw [hgt] at hgo
        dsimp only at hgo
        rw [hgv] at hgo
        dsimp only at hgo
        rw [hgb] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨rfl, hinv₃.insert hx, hlinv₃⟩
      | proj s j e' =>
        rw [denoteNode, Option.map_eq_some_iff] at hd
        obtain ⟨xe, he, rfl⟩ := hd
        have hlt : e' < e := hc e' (by simp [ENode.children])
        dsimp only at hgo
        rw [dif_pos hlt] at hgo
        rcases hge : readbackGo st memo lmemo e' with ⟨re, memo₁, lmemo₁⟩
        obtain ⟨rfl, hinv₁, hlinv₁⟩ := ih e' hlt he hinv hlinv hge
        rw [hge] at hgo
        dsimp only at hgo
        injection hgo with h1 h2
        injection h2 with h2 h3
        subst h1; subst h2; subst h3
        exact ⟨rfl, hinv₁.insert hx, hlinv₁⟩

/-- On a well-formed store, `readbackI` computes the denotation. -/
theorem readbackI_spec {st : EStore} (hwf : st.WF) {e : EIdx} {x : Expr}
    (hx : st.denote e = some x) : st.readbackI e = some x := by
  rcases hgo : readbackGo st {} {} e with ⟨r, memo', lmemo'⟩
  obtain ⟨rfl, -, -⟩ := readbackGo_spec hwf e hx RInv.empty RLInv.empty hgo
  rw [readbackI, hgo]


/-! ## The `FEnv` index agrees with `Env.find?` -/

private theorem foldr_index_find? (n : Name) :
    ∀ (l : List ConstantInfo),
      (l.foldr (fun ci m => m.insert ci.name ci)
        (∅ : Std.HashMap Name ConstantInfo))[n]? =
        l.find? (fun ci => ci.name == n)
  | [] => by simp
  | ci :: l => by
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, List.find?_cons]
    by_cases hn : ci.name == n
    · rw [if_pos hn, hn]
    · rw [if_neg hn, foldr_index_find? n l]
      rw [show (ci.name == n) = false by simpa using hn]

/-- The per-entry-call name index computes `Env.find?`. -/
theorem mkFEnv_find? (env : Env) (n : Name) :
    (mkFEnv env).find? n = env.find? n :=
  foldr_index_find? n env.consts

/-- The indexed projection lookup computes `Env.findProj?`. -/
theorem mkFEnv_findProj? (env : Env) (T : Name) (i : Nat) :
    (mkFEnv env).findProj? T i = env.findProj? T i := by
  rw [FEnv.findProj?, Env.findProj?, mkFEnv_find?]
  rfl

/-! ## Guard twins agree with the `Env` versions -/

theorem natLitSupportedF_eq (env : Env) :
    natLitSupportedF (mkFEnv env) = natLitSupported env := by
  simp only [natLitSupportedF, natLitSupported, mkFEnv_find?]

theorem strLitSupportedF_eq (env : Env) :
    strLitSupportedF (mkFEnv env) = strLitSupported env := by
  simp only [strLitSupportedF, strLitSupported, mkFEnv_find?,
    natLitSupportedF_eq]

theorem natOpGuardF_eq (env : Env) (c : Name) :
    natOpGuardF (mkFEnv env) c = natOpGuard env c := by
  simp only [natOpGuardF, natOpGuard, mkFEnv_find?, natLitSupportedF_eq]
  rfl

/-! ## Node classifiers agree with the `Expr` versions -/

theorem isUnitLikeTyI_spec {st : EStore} {env : Env} {e : EIdx} {x : Expr}
    (_hwf : st.WF) (hx : st.denote e = some x) :
    isUnitLikeTyI (mkFEnv env) st e = isUnitLikeTy env x := by
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hx
  rw [isUnitLikeTyI, hn]
  cases n with
  | const nm us =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lus, _, rfl⟩ := hd
    dsimp only
    rw [show isUnitLikeTy env (.const nm lus) =
      ((match env.find? nm with
        | some (.indInfo _ _) => true
        | _ => false) &&
      (match env.find? (nm.str "rec") with
        | some (.recInfo _ mI rP [r]) => mI == rP && r.nfields == 0
        | _ => false) &&
      reservedBasisNames.contains (nm.str "rec")) from rfl]
    rw [mkFEnv_find?, mkFEnv_find?]
    rfl
  | bvar i => cases hd; rfl
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, _, rfl⟩ := hd
    rfl
  | lit l => cases hd; rfl
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨t', _, rfl⟩ := hd
    rfl
  | app f a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, rfl⟩ := hd
    rfl
  | lam nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bm, hbm', rfl⟩ := hd
    rfl
  | forallE nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bm, hbm', rfl⟩ := hd
    rfl
  | letE nm t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, rfl⟩ := hd
    rfl
  | proj s j e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨ee, _, rfl⟩ := hd
    rfl

/-- A denoted head node is the denotation's `getAppFn` head shape:
convenience inversion pairing `getAppFnI_spec` with `denote_some_inv`. -/
theorem head_node_spec {st : EStore} (hwf : st.WF) {e : EIdx} {x : Expr}
    (hx : st.denote e = some x) :
    ∃ n, st.nodes[st.getAppFnI e]? = some n ∧
      denoteNode st.denote st.denoteL n = some x.getAppFn := by
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hwf hx)
  exact ⟨n, hn, hd⟩

theorem isCtorAppI_spec {st : EStore} {env : Env} {e : EIdx} {x : Expr}
    (hwf : st.WF) (hx : st.denote e = some x) :
    isCtorAppI (mkFEnv env) st e = isCtorApp env x := by
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hwf hx)
  rw [isCtorAppI, hn, isCtorApp]
  cases n with
  | const nm us =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lus, _, hd⟩ := hd
    rw [← hd]
    dsimp only
    rw [mkFEnv_find?]
    rfl
  | bvar i =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, _, hd⟩ := hd
    rw [← hd]
  | lit l =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨t', _, hd⟩ := hd
    rw [← hd]
  | app f a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, hd⟩ := hd
    rw [← hd]
  | lam nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bm, _, hd⟩ := hd
    rw [← hd]
  | forallE nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bm, _, hd⟩ := hd
    rw [← hd]
  | letE nm t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]
  | proj s j e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨ee, _, hd⟩ := hd
    rw [← hd]

theorem headHintI_spec {st : EStore} {env : Env} {e : EIdx} {x : Expr}
    (hwf : st.WF) (hx : st.denote e = some x) :
    headHintI (mkFEnv env) st e = headHint env x := by
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hwf hx)
  rw [headHintI, hn, headHint]
  cases n with
  | const nm us =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lus, _, hd⟩ := hd
    rw [← hd]
    dsimp only
    rw [mkFEnv_find?]
    rfl
  | bvar i =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, _, hd⟩ := hd
    rw [← hd]
  | lit l =>
    rw [denoteNode] at hd
    have h := Option.some.inj hd
    rw [← h]
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨t', _, hd⟩ := hd
    rw [← hd]
  | app f a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, hd⟩ := hd
    rw [← hd]
  | lam nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bm, _, hd⟩ := hd
    rw [← hd]
  | forallE nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bm, _, hd⟩ := hd
    rw [← hd]
  | letE nm t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [← hd]
  | proj s j e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨ee, _, hd⟩ := hd
    rw [← hd]

theorem rawNatLitI?_spec {st : EStore} {e : EIdx} {x : Expr}
    (hx : st.denote e = some x) :
    rawNatLitI? st e = rawNatLit? x := by
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv hx
  rw [rawNatLitI?, hn]
  cases n with
  | const nm us =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lus, hlus, rfl⟩ := hd
    cases us with
    | nil => cases hlus; rfl
    | cons u us' =>
      simp only [denoteLList, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hlus
      obtain ⟨l, -, ls, -, rfl⟩ := hlus
      rfl
  | bvar i => cases hd; rfl
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lu, _, rfl⟩ := hd
    rfl
  | lit l =>
    cases hd
    cases l with
    | natVal k => rfl
    | strVal s => rfl
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨t', _, rfl⟩ := hd
    rfl
  | app f a =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨ef, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨ea, _, rfl⟩ := hd
    rfl
  | lam nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bm, hbm', rfl⟩ := hd
    rfl
  | forallE nm t b m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨eb, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨bm, hbm', rfl⟩ := hd
    rfl
  | letE nm t v b =>
    rw [denoteNode, Option.bind_eq_some_iff] at hd
    obtain ⟨et, _, hd⟩ := hd
    rw [Option.bind_eq_some_iff] at hd
    obtain ⟨ev, _, hd⟩ := hd
    rw [Option.map_eq_some_iff] at hd
    obtain ⟨eb, _, rfl⟩ := hd
    rfl
  | proj s j e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨ee, _, rfl⟩ := hd
    rfl

theorem sameConstHeadsI_spec {st : EStore} {a b : EIdx} {xa xb : Expr}
    (hwf : st.WF) (ha : st.denote a = some xa) (hb : st.denote b = some xb) :
    sameConstHeadsI st a b = sameConstHeads xa xb := by
  obtain ⟨na, hna, hca, hda⟩ := denote_some_inv ha
  obtain ⟨nb, hnb, hcb, hdb⟩ := denote_some_inv hb
  rw [sameConstHeadsI, hna, hnb]
  cases na with
  | app f₁ a₁ =>
    rw [denoteNode, Option.bind_eq_some_iff] at hda
    obtain ⟨xf₁, hf₁, hda⟩ := hda
    rw [Option.map_eq_some_iff] at hda
    obtain ⟨xa₁, ha₁, rfl⟩ := hda
    cases nb with
    | app f₂ a₂ =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdb
      obtain ⟨xf₂, hf₂, hdb⟩ := hdb
      rw [Option.map_eq_some_iff] at hdb
      obtain ⟨xa₂, ha₂, rfl⟩ := hdb
      rw [show sameConstHeads (.app xf₁ xa₁) (.app xf₂ xa₂) =
        (match xf₁.getAppFn, xf₂.getAppFn with
          | .const n₁ _, .const n₂ _ => n₁ == n₂
          | _, _ => false) from rfl]
      obtain ⟨m₁, hm₁, -, hdm₁⟩ := denote_some_inv (getAppFnI_spec hwf hf₁)
      obtain ⟨m₂, hm₂, -, hdm₂⟩ := denote_some_inv (getAppFnI_spec hwf hf₂)
      dsimp only
      rw [hm₁, hm₂]
      cases m₁ with
      | const n₁ us₁ =>
        rw [denoteNode, Option.map_eq_some_iff] at hdm₁
        obtain ⟨lus₁, _, h₁⟩ := hdm₁
        cases m₂ with
        | const n₂ us₂ =>
          rw [denoteNode, Option.map_eq_some_iff] at hdm₂
          obtain ⟨lus₂, _, h₂⟩ := hdm₂
          rw [← h₁, ← h₂]
        | bvar i => rw [← Option.some.inj hdm₂, ← h₁]
        | sort u =>
          rw [denoteNode, Option.map_eq_some_iff] at hdm₂
          obtain ⟨lu, _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
        | lit l => rw [← Option.some.inj hdm₂, ← h₁]
        | fvar idx nm t =>
          rw [denoteNode, Option.map_eq_some_iff] at hdm₂
          obtain ⟨t', _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
        | app f a' =>
          rw [denoteNode, Option.bind_eq_some_iff] at hdm₂
          obtain ⟨ef, _, hdm₂⟩ := hdm₂
          rw [Option.map_eq_some_iff] at hdm₂
          obtain ⟨ea, _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
        | lam nm t b' m =>
          rw [denoteNode, Option.bind_eq_some_iff] at hdm₂
          obtain ⟨et, _, hdm₂⟩ := hdm₂
          rw [Option.bind_eq_some_iff] at hdm₂
          obtain ⟨eb, _, hdm₂⟩ := hdm₂
          rw [Option.map_eq_some_iff] at hdm₂
          obtain ⟨bm, _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
        | forallE nm t b' m =>
          rw [denoteNode, Option.bind_eq_some_iff] at hdm₂
          obtain ⟨et, _, hdm₂⟩ := hdm₂
          rw [Option.bind_eq_some_iff] at hdm₂
          obtain ⟨eb, _, hdm₂⟩ := hdm₂
          rw [Option.map_eq_some_iff] at hdm₂
          obtain ⟨bm, _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
        | letE nm t v b' =>
          rw [denoteNode, Option.bind_eq_some_iff] at hdm₂
          obtain ⟨et, _, hdm₂⟩ := hdm₂
          rw [Option.bind_eq_some_iff] at hdm₂
          obtain ⟨ev, _, hdm₂⟩ := hdm₂
          rw [Option.map_eq_some_iff] at hdm₂
          obtain ⟨eb, _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
        | proj s j e' =>
          rw [denoteNode, Option.map_eq_some_iff] at hdm₂
          obtain ⟨ee, _, hdm₂⟩ := hdm₂
          rw [← hdm₂, ← h₁]
      | bvar i =>
        rw [← Option.some.inj hdm₁]
      | sort u =>
        rw [denoteNode, Option.map_eq_some_iff] at hdm₁
        obtain ⟨lu, _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
      | lit l =>
        rw [← Option.some.inj hdm₁]
      | fvar idx nm t =>
        rw [denoteNode, Option.map_eq_some_iff] at hdm₁
        obtain ⟨t', _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
      | app f a' =>
        rw [denoteNode, Option.bind_eq_some_iff] at hdm₁
        obtain ⟨ef, _, hdm₁⟩ := hdm₁
        rw [Option.map_eq_some_iff] at hdm₁
        obtain ⟨ea, _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
      | lam nm t b' m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hdm₁
        obtain ⟨et, _, hdm₁⟩ := hdm₁
        rw [Option.bind_eq_some_iff] at hdm₁
        obtain ⟨eb, _, hdm₁⟩ := hdm₁
        rw [Option.map_eq_some_iff] at hdm₁
        obtain ⟨bm, _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
      | forallE nm t b' m =>
        rw [denoteNode, Option.bind_eq_some_iff] at hdm₁
        obtain ⟨et, _, hdm₁⟩ := hdm₁
        rw [Option.bind_eq_some_iff] at hdm₁
        obtain ⟨eb, _, hdm₁⟩ := hdm₁
        rw [Option.map_eq_some_iff] at hdm₁
        obtain ⟨bm, _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
      | letE nm t v b' =>
        rw [denoteNode, Option.bind_eq_some_iff] at hdm₁
        obtain ⟨et, _, hdm₁⟩ := hdm₁
        rw [Option.bind_eq_some_iff] at hdm₁
        obtain ⟨ev, _, hdm₁⟩ := hdm₁
        rw [Option.map_eq_some_iff] at hdm₁
        obtain ⟨eb, _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
      | proj s j e' =>
        rw [denoteNode, Option.map_eq_some_iff] at hdm₁
        obtain ⟨ee, _, hdm₁⟩ := hdm₁
        rw [← hdm₁]
    | bvar i => cases hdb; rfl
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hdb
      obtain ⟨lu, _, rfl⟩ := hdb
      rfl
    | const nm us =>
      rw [denoteNode, Option.map_eq_some_iff] at hdb
      obtain ⟨lus, _, rfl⟩ := hdb
      rfl
    | lit l => cases hdb; rfl
    | fvar idx nm t =>
      rw [denoteNode, Option.map_eq_some_iff] at hdb
      obtain ⟨t', _, rfl⟩ := hdb
      rfl
    | lam nm t b' m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdb
      obtain ⟨et, _, hdb⟩ := hdb
      rw [Option.bind_eq_some_iff] at hdb
      obtain ⟨eb, _, hdb⟩ := hdb
      rw [Option.map_eq_some_iff] at hdb
      obtain ⟨bm, _, rfl⟩ := hdb
      rfl
    | forallE nm t b' m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdb
      obtain ⟨et, _, hdb⟩ := hdb
      rw [Option.bind_eq_some_iff] at hdb
      obtain ⟨eb, _, hdb⟩ := hdb
      rw [Option.map_eq_some_iff] at hdb
      obtain ⟨bm, _, rfl⟩ := hdb
      rfl
    | letE nm t v b' =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdb
      obtain ⟨et, _, hdb⟩ := hdb
      rw [Option.bind_eq_some_iff] at hdb
      obtain ⟨ev, _, hdb⟩ := hdb
      rw [Option.map_eq_some_iff] at hdb
      obtain ⟨eb, _, rfl⟩ := hdb
      rfl
    | proj s j e' =>
      rw [denoteNode, Option.map_eq_some_iff] at hdb
      obtain ⟨ee, _, rfl⟩ := hdb
      rfl
  | bvar i => cases hda; rfl
  | sort u =>
    rw [denoteNode, Option.map_eq_some_iff] at hda
    obtain ⟨lu, _, rfl⟩ := hda
    rfl
  | const nm us =>
    rw [denoteNode, Option.map_eq_some_iff] at hda
    obtain ⟨lus, _, rfl⟩ := hda
    rfl
  | lit l => cases hda; rfl
  | fvar idx nm t =>
    rw [denoteNode, Option.map_eq_some_iff] at hda
    obtain ⟨t', _, rfl⟩ := hda
    rfl
  | lam nm t b' m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hda
    obtain ⟨et, _, hda⟩ := hda
    rw [Option.bind_eq_some_iff] at hda
    obtain ⟨eb, _, hda⟩ := hda
    rw [Option.map_eq_some_iff] at hda
    obtain ⟨bm, _, rfl⟩ := hda
    rfl
  | forallE nm t b' m =>
    rw [denoteNode, Option.bind_eq_some_iff] at hda
    obtain ⟨et, _, hda⟩ := hda
    rw [Option.bind_eq_some_iff] at hda
    obtain ⟨eb, _, hda⟩ := hda
    rw [Option.map_eq_some_iff] at hda
    obtain ⟨bm, _, rfl⟩ := hda
    rfl
  | letE nm t v b' =>
    rw [denoteNode, Option.bind_eq_some_iff] at hda
    obtain ⟨et, _, hda⟩ := hda
    rw [Option.bind_eq_some_iff] at hda
    obtain ⟨ev, _, hda⟩ := hda
    rw [Option.map_eq_some_iff] at hda
    obtain ⟨eb, _, rfl⟩ := hda
    rfl
  | proj s j e' =>
    rw [denoteNode, Option.map_eq_some_iff] at hda
    obtain ⟨ee, _, rfl⟩ := hda
    rfl

/-! ## The fabrication leaf-subset guard -/

/-- The `Expr`-side leaf list lifted to `Option` types. -/
def leavesL (A : List (Nat × Name × Expr)) : List (Nat × Name × Option Expr) :=
  A.map fun l => (l.1, l.2.1, some l.2.2)

theorem leavesExp_eq_leavesL (x : Expr) : leavesExp x = leavesL x.fvarLeaves :=
  rfl

/-- Membership transfer along the denotation of leaf lists (denotation
is injective on well-formed stores, so `contains` transfers in both
directions). -/
private theorem leaves_contains {st : EStore} (hwf : st.WF)
    {B : List (Nat × Name × EIdx)} {B' : List (Nat × Name × Expr)}
    (hB : leavesDen st B = leavesL B')
    {l : Nat × Name × EIdx} {x : Expr} (hx : st.denote l.2.2 = some x) :
    B.contains l = B'.contains (l.1, l.2.1, x) := by
  rcases l with ⟨i, nm, t⟩
  simp only at hx
  simp only [List.contains_eq_mem, decide_eq_decide]
  constructor
  · intro hmem
    have hmm : ((i, nm, st.denote t) : Nat × Name × Option Expr)
        ∈ leavesL B' := by
      rw [← hB]
      exact List.mem_map_of_mem hmem
    obtain ⟨⟨a, b, c⟩, hl', heq⟩ := List.mem_map.mp hmm
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, hc⟩ := heq
    rw [hx] at hc
    obtain rfl : c = x := Option.some.inj hc
    exact hl'
  · intro hmem
    have hmm : ((i, nm, some x) : Nat × Name × Option Expr)
        ∈ leavesDen st B := by
      rw [hB]
      exact List.mem_map_of_mem hmem
    obtain ⟨⟨a, b, c⟩, hl', heq⟩ := List.mem_map.mp hmm
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, hc⟩ := heq
    obtain rfl : c = t := denote_inj hwf hc hx
    exact hl'

/-- The fabrication-side memoized subset walk agrees with the
`Expr`-level `.all`-over-`fvarLeaves` boolean (task #86), given a
base leaf list that denotes `B'`. -/
private theorem leavesSubIGo_spec {st : EStore} (hwf : st.WF)
    {B : List (Nat × Name × EIdx)} {B' : List (Nat × Name × Expr)}
    (hB : leavesDen st B = leavesL B') :
    ∀ (e : EIdx) {memo : Std.HashMap EIdx Bool} {r : Bool}
      {memo' : Std.HashMap EIdx Bool},
      QMemo0Inv st (fun x => x.fvarLeaves.all fun l => B'.contains l) memo →
      leavesSubIGo st B memo e = (r, memo') →
      QMemo0Inv st (fun x => x.fvarLeaves.all fun l => B'.contains l) memo' ∧
        ∀ x, st.denote e = some x →
          r = (x.fvarLeaves.all fun l => B'.contains l) := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro memo r memo' hinv hgo
    unfold EStore.leavesSubIGo at hgo
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
              true = (x.fvarLeaves.all fun l => B'.contains l) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.fvarLeaves]
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
              true = (x.fvarLeaves.all fun l => B'.contains l) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.fvarLeaves]
          exact ⟨hinv.insert hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun v hv => hwf.levels_lt e _ hn v (by simp [ENode.levels, hv]))
          have hx : st.denote e = some (.const nm lus) := by
            rw [hde, denoteNode, hlus]; rfl
          have hcond : ∀ x, st.denote e = some x →
              true = (x.fvarLeaves.all fun l => B'.contains l) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.fvarLeaves]
          exact ⟨hinv.insert hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              true = (x.fvarLeaves.all fun l => B'.contains l) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.fvarLeaves]
          exact ⟨hinv.insert hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          obtain ⟨xt, hxt⟩ := denote_total hwf t
            (Nat.lt_trans (hcl t (by simp [ENode.children])) hesz)
          have hx : st.denote e = some (.fvar idx nm xt) := by
            rw [hde, denoteNode, hxt]; rfl
          have hcont : B.contains (idx, nm, t)
              = B'.contains (idx, nm, xt) :=
            leaves_contains hwf hB (l := (idx, nm, t)) hxt
          split at hgo
          · rename_i hin
            split at hgo
            · rename_i hlt
              rcases h₁ : EStore.leavesSubIGo st B memo t with ⟨rt, memo₁⟩
              rw [h₁] at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₁, hden₁⟩ := ih t hlt hinv h₁
              have hcond : ∀ x, st.denote e = some x →
                  rt = (x.fvarLeaves.all fun l => B'.contains l) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [hin] at hcont
                rw [hden₁ xt hxt]
                simp only [Expr.fvarLeaves, List.all_cons, ← hcont,
                  Bool.true_and]
              exact ⟨hinv₁.insert hcond, hcond⟩
            · rename_i hlt
              exact absurd (hcl t (by simp [ENode.children])) hlt
          · rename_i hin
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            have hcond : ∀ x, st.denote e = some x →
                false = (x.fvarLeaves.all fun l => B'.contains l) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [Bool.not_eq_true] at hin
              rw [hin] at hcont
              simp only [Expr.fvarLeaves, List.all_cons, ← hcont,
                Bool.false_and]
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
            rcases h₁ : EStore.leavesSubIGo st B memo f with ⟨rf, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih f hguard.1 hinv h₁
            split at hgo
            · rename_i hrf
              rcases h₂ : EStore.leavesSubIGo st B memo₁ a with ⟨ra, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih a hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  ra = (x.fvarLeaves.all fun l => B'.contains l) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [hrf] at h1
                rw [hden₂ xa ha]
                simp only [Expr.fvarLeaves, List.all_append, ← h1,
                  Bool.true_and]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrf
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = (x.fvarLeaves.all fun l => B'.contains l) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [Bool.not_eq_true] at hrf
                rw [hrf] at h1
                simp only [Expr.fvarLeaves, List.all_append, ← h1,
                  Bool.false_and]
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
            have hx : st.denote e = some (.lam nm xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm]; rfl
            rcases h₁ : EStore.leavesSubIGo st B memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : EStore.leavesSubIGo st B memo₁ body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  rb = (x.fvarLeaves.all fun l => B'.contains l) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                rw [hden₂ xb hb]
                simp only [Expr.fvarLeaves, List.all_append, ← h1,
                  Bool.true_and]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = (x.fvarLeaves.all fun l => B'.contains l) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp only [Expr.fvarLeaves, List.all_append, ← h1,
                  Bool.false_and]
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
            have hx : st.denote e = some (.forallE nm xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm]; rfl
            rcases h₁ : EStore.leavesSubIGo st B memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : EStore.leavesSubIGo st B memo₁ body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  rb = (x.fvarLeaves.all fun l => B'.contains l) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                rw [hden₂ xb hb]
                simp only [Expr.fvarLeaves, List.all_append, ← h1,
                  Bool.true_and]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = (x.fvarLeaves.all fun l => B'.contains l) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp only [Expr.fvarLeaves, List.all_append, ← h1,
                  Bool.false_and]
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
            obtain ⟨xv, hvv⟩ := denote_total hwf val
              (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body
              (Nat.lt_trans hguard.2.2 hesz)
            have hx : st.denote e = some (.letE nm xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb]; rfl
            rcases h₁ : EStore.leavesSubIGo st B memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : EStore.leavesSubIGo st B memo₁ val with ⟨rv, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              obtain ⟨hinv₂, hden₂⟩ := ih val hguard.2.1 hinv₁ h₂
              split at hgo
              · rename_i hrv
                rcases h₃ : EStore.leavesSubIGo st B memo₂ body
                  with ⟨rb, memo₃⟩
                rw [h₃] at hgo
                try dsimp only at hgo
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                obtain ⟨hinv₃, hden₃⟩ := ih body hguard.2.2 hinv₂ h₃
                have hcond : ∀ x, st.denote e = some x →
                    rb = (x.fvarLeaves.all fun l => B'.contains l) := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h1 := hden₁ xt ht
                  have h2 := hden₂ xv hvv
                  rw [hrt] at h1
                  rw [hrv] at h2
                  rw [hden₃ xb hb]
                  simp only [Expr.fvarLeaves, List.all_append, ← h1,
                    ← h2, Bool.true_and]
                exact ⟨hinv₃.insert hcond, hcond⟩
              · rename_i hrv
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                have hcond : ∀ x, st.denote e = some x →
                    false = (x.fvarLeaves.all fun l => B'.contains l) := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h2 := hden₂ xv hvv
                  rw [Bool.not_eq_true] at hrv
                  rw [hrv] at h2
                  simp only [Expr.fvarLeaves, List.all_append, ← h2,
                    Bool.and_false, Bool.false_and]
                exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = (x.fvarLeaves.all fun l => B'.contains l) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp only [Expr.fvarLeaves, List.all_append, ← h1,
                  Bool.false_and]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hx : st.denote e = some (.proj s j xs) := by
              rw [hde, denoteNode, hs]; rfl
            rcases h₁ : EStore.leavesSubIGo st B memo sub with ⟨rs, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih sub hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x →
                rs = (x.fvarLeaves.all fun l => B'.contains l) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.fvarLeaves] using hden₁ xs hs
            exact ⟨hinv₁.insert hcond, hcond⟩

/-- `hasFvar = false` forces an empty leaf list (local copy of
`Expr.fvarLeaves_eq_nil_of_not_hasFvar`; `Verify/Leaves.lean` sits
higher in the import graph). -/
private theorem fvarLeaves_nil_of_not_hasFvar :
    ∀ {e : Expr}, e.hasFvar = false → e.fvarLeaves = [] := by
  intro e
  induction e <;> simp_all [Expr.hasFvar, Expr.fvarLeaves]

/-- The interned fabrication guard (`leafGuardI`: `hasFvarI`
short-circuit over the memoized fabrication-side subset walk, tasks
#84/#86) agrees with the `Expr`-level leaf-subset boolean. -/
theorem leafGuardI_spec {st : EStore} (hwf : st.WF) {fab base : EIdx}
    {xf xb : Expr} (hf : st.denote fab = some xf)
    (hb : st.denote base = some xb) :
    st.leafGuardI fab base
      = (xf.fvarLeaves.all fun l => xb.fvarLeaves.contains l) := by
  unfold EStore.leafGuardI
  rw [hasFvarI_spec hwf hf]
  cases hhf : xf.hasFvar with
  | false =>
    simp [fvarLeaves_nil_of_not_hasFvar hhf]
  | true =>
    have hB := (fvarLeavesI_spec hwf hb).trans (leavesExp_eq_leavesL xb)
    rcases hgo : EStore.leavesSubIGo st (st.fvarLeavesI base) {} fab
      with ⟨r, memo'⟩
    obtain ⟨-, hcond⟩ := leavesSubIGo_spec hwf hB fab QMemo0Inv.empty hgo
    simp only [hgo, Bool.not_true, Bool.false_or]
    exact hcond xf hf
end Setlec
